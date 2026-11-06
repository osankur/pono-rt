#include "core/tts.h"

#include <cassert>
#include "utils/logger.h"
#include "smt-switch/term.h"
using namespace smt;
namespace pono {
const std::string TimedTransitionSystem::DELAY_VAR_NAME = "_DELTA_";

std::string to_string(TADelayStrictness strictness){
    switch(strictness) {
        case TADelayStrictness::Strict : return "Strict";
        case TADelayStrictness::Weak : return "Weak";
        case TADelayStrictness::GeqOne : return "GeqOne";
    }
    return "Unknown";
}


void TimedTransitionSystem::encode_timed_automaton_delays()
{
  if (encoded_delays_) return;
  this->encoded_delays_ = true;
  encode_compact_delays();
}
void TimedTransitionSystem::constrain_invariant(const Term & constraint)
{
  // TODO: Only do this check in debug mode
  if (!known_symbols(constraint)) {
    throw PonoException("Unknown symbols");
  }
  if (invariant_ == nullptr) invariant_ = solver_->make_term(true);
  invariant_ = solver_->make_term(And, invariant_, constraint);
}
const smt::Term TimedTransitionSystem::invariant(){
  return invariant_;
}
void TimedTransitionSystem::add_dummy_init_transitions(){
  assert(!this->has_dummy_init_transitions_);
  this->has_dummy_init_transitions_ = true;

  smt::Term dummy_transition = solver_->make_term(true);  
  for (auto v : statevars_) {
    smt::Term vunchanged = solver_->make_term(Equal, v, next(v));
    dummy_transition = solver_->make_term(And, dummy_transition, vunchanged);
  }
  dummy_transition = solver_->make_term(And, dummy_transition, init());
  logger.log(4, "Dummy transitions: {}", dummy_transition);
  // dummy_transition = X'=X/\ C'=C /\ init
  // trans := trans \/ dummy_transition
  set_trans(solver_->make_term(Or, trans(), dummy_transition));
}

void TimedTransitionSystem::encode_compact_delays(){
  smt::Sort realsort = solver_->make_sort(smt::REAL);
  smt::Sort intsort = solver_->make_sort(smt::INT);

  // determine the sort of clocks (and thus that of delays): int or real
  if (clock_vars_.size() > 0){
    smt::Term clock = *clock_vars_.begin();
    this->delay_sort_ = clock->get_sort();
    if (this->delay_sort_ != realsort && this->delay_sort_ != intsort){
      throw PonoException("Clocks must be of sort Int or Real: " + clock->to_string());
    }
    for (auto c : clock_vars_){
      if ( c->get_sort() != this->delay_sort_){
        throw PonoException("All clocks must have the same sort: "+ c->to_string());
      }
    }
  }

  delta_ = TransitionSystem::make_inputvar(DELAY_VAR_NAME, this->delay_sort_);
  logger.log(1, "Sort of timed automata clocks: {}", this->delay_sort_);
  logger.log(1, "Unit delays: {}", this->getDelayType() == TimedAutomatonDelays::UnitDurations);
  logger.log(1, "Delays are strict/weak/geqOne: {}", to_string(TADelayStrictness::Strict));
  logger.log(1, "Delay-First: {}", this->delay_edge_order_ == TADelayEdgeOrder::DelayFirst);
  logger.log(2, "Listing timed automata clocks:");
  for (auto c : clock_vars_){
    logger.log(2, "\t{}", c);
  }

  if ( delay_edge_order_ == TADelayEdgeOrder::DelaySecond){
    logger.log(1, "Adding dummy initial transition (this allows starting the run with a delay)");
    // add a dummy edge to the init discrete location to allow delays at the beginning of an execution
    add_dummy_init_transitions();
  } 


  smt::Term zero, one;
  if (delay_sort_->get_sort_kind() == smt::REAL) {
    zero = solver_->make_term(To_Real, solver_->make_term("0", solver_->make_sort(INT)));
    one = solver_->make_term(To_Real, solver_->make_term("1", solver_->make_sort(INT)));
  } else {
    zero = solver_->make_term("0", solver_->make_sort(INT));
    one = solver_->make_term("1", solver_->make_sort(INT));
  }
  smt::Term clocks_nonnegative = solver_->make_term(true);
  smt::Term clocks_are_zero = solver_->make_term(true);
  for (auto c : clock_vars_) {
    clocks_are_zero = 
      solver_->make_term(And, 
        clocks_are_zero, 
        solver_->make_term(Equal, c, zero));
    clocks_nonnegative = 
      solver_->make_term(And, 
        clocks_nonnegative, 
          solver_->make_term(Ge, c, zero)
      );
  }

  /*   DelayFirst:
     *
     * T(C,X, I, C',X') =
     *    C >= 0 
     * /\ delta >= 0 
     * /\ locinvar(C+delta,X)          '
     * /\ (urgent(X) -> delta = 0)     '
     * /\ (trans(C+delta,X,I,C',X')    '
     * /\ locinvar(X',C')
     * (/\ delta = 1) if UnitDurations
  */
  /*   DelaySecond:
     *
     * T(C,X, I, C',X') =
     *    C >= 0 
     * /\ delta >= 0 
     * /\ locinvar(C,X)
     * /\ (urgent(X') -> delta = 0) 
     * /\ (trans(C,X,I,C'-delta,X')
     * /\ locinvar(X',C')
     * (/\ delta = 1) if UnitDurations
     */

  // /\ C >= 0
  smt::Term new_trans = solver_->make_term(And, clocks_nonnegative, next(clocks_nonnegative));
  logger.log(4, "TA Clock >= 0: {}", new_trans);

  smt::Term delta_nonnegative;
  if (this->delay_type_ == TimedAutomatonDelays::ArbitraryDurations){
    if (this->delay_strictness_ == TADelayStrictness::Weak)
      delta_nonnegative = solver_->make_term(Le, zero, delta_);
    else if(this->delay_strictness_ == TADelayStrictness::Strict)
      delta_nonnegative = solver_->make_term(Lt, zero, delta_);
    else 
      delta_nonnegative = solver_->make_term(Le, one, delta_);
  } else {
    delta_nonnegative = solver_->make_term(Equal, one, delta_);
  }  
  logger.log(4, "TA delta >= 0, delta > 0, or delta=1: {}", delta_nonnegative);

  // /\ delta >= 0
  new_trans = solver_->make_term(And, new_trans, delta_nonnegative);

  smt::Term delta0ifurgent = solver_->make_term(true);
  if (delay_edge_order_ == TADelayEdgeOrder::DelaySecond){
    // DelaySecond: /\ (urgent(X') -> delta = 0) 
    solver_->make_term(Implies, next(urgent()), solver_->make_term(Equal, delta_, zero));
  } else {
    // DelayFirst: /\ (urgent(X) -> delta = 0) 
    solver_->make_term(Implies, urgent(), solver_->make_term(Equal, delta_, zero));
  }
  new_trans = solver_->make_term(And, new_trans, delta0ifurgent);
  logger.log(4, "TA delta0ifurgent: {}", delta0ifurgent);

  smt::UnorderedTermMap Cp2Cp_minus_delta;
  smt::UnorderedTermMap C2C_plus_delta;
  for (auto c : clock_vars_) {
    Cp2Cp_minus_delta[next(c)] = solver_->make_term(Minus, next(c), delta_);
    C2C_plus_delta[c] = solver_->make_term(Plus, c, delta_);
  }
  logger.log(4, "TA Cp2Cp_minus_delta: {}", solver_->substitute(trans(), Cp2Cp_minus_delta));

  if (delay_edge_order_ == TADelayEdgeOrder::DelaySecond){
    // DelaySecond: /\ (trans(C,X,I,C'-delta,X')
    new_trans = solver_->make_term(And, new_trans, solver_->substitute(trans(), Cp2Cp_minus_delta));
    // /\ locinvar(C,X)
    new_trans = solver_->make_term(And, new_trans, locinvar());
  } else {
    // DelayFirst: /\ (trans(C+delta,X,I,C',X')
    new_trans = solver_->make_term(And, new_trans, solver_->substitute(trans(), C2C_plus_delta));
    // /\ locinvar(C+delta,X)
    new_trans = solver_->make_term(And, new_trans, solver_->substitute(locinvar(), C2C_plus_delta));
  }
  
  // /\ locinvar(C',X')
  new_trans = solver_->make_term(And, new_trans, next(locinvar()));
  set_trans(new_trans);
  set_init(solver_->make_term(And, init(), clocks_are_zero));

  // init = init /\ C = 0
  logger.log(4, "TA Init: {}", init());
  logger.log(4, "TA locinvar: {}", locinvar());
  logger.log(4, "TA urgent: {}", urgent());
}
}  // namespace pono