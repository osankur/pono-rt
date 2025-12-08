/*********************                                                  */
/*! \file IC3IAQ.cpp
** \brief IC3IA applied to rt-consistency checking.
** \author Ocan Sankur <ocan.sankur@cnrs.fr>
**
**/

#include "engines/ic3iartc.h"

#include <random>

#include <string>
#include "smt/available_solvers.h"
#include "smt/external_interpolator.h"
#include "utils/logger.h"
#include "utils/term_analysis.h"

using namespace smt;
using namespace std;

namespace pono {

IC3IAQ::IC3IAQ(const Property & p,
                   const TransitionSystem & ts,
                   const SmtSolver & s,
                   PonoOptions opt
                   )
     : IC3IA(p, ts, s, opt), external_interpolator_(interpolator_, opt.external_interpolator_)
{
  logger.log(1, "Engine: IC3IAQ");
  engine_ = Engine::IC3IAQ_ENGINE;
  assert(ts_.solver() == orig_property_.solver());
}

/**
 * This is a copy of IC3IA::reconstruct_trace with the following difference.
 * Rather than adding bad at the end of the trace, we actually extract a bad
 * state that is reachable from the penultimate step. This helps us avoid having
 * a quantified formula in the trace.
 */
void IC3IAQ::reconstruct_trace(const ProofGoal * pg, TermVec & out)
{
  assert(!solver_context_);
  assert(pg);
  assert(pg->target.term);
  assert(check_intersects_initial(pg->target.term));

  logger.log(2, "IC3IAQ::reconstruct_trace\n");
  out.clear();
  while (pg) {
    out.push_back(pg->target.term);
    assert(ts_.only_curr(out.back()));
    pg = pg->next;
  }

  push_solver_context();
  smt::Term next_bad = ts_.next(bad_);

  solver_->assert_formula(out.back());
  solver_->assert_formula(ts_.trans());
  solver_->assert_formula(next_bad);
  Result r = check_sat();
  assert(r.is_sat());

  Term prebad = get_nextstate_model();
  out.push_back(prebad);
  pop_solver_context();

  logger.log(3, "\nAbstract trace:");
  for (auto t : out ){
    logger.log(3, t->to_string());
  }
}

/**
 * This is a copy of the IC3IA::refine function which can call an alternative interpolator.
 * We keep this as a copy here in order to minimize modifications to the core of Pono,
 * and because we have, for now, light-weight interfaces to alternative interpolators.
*/
RefineResult IC3IAQ::refine()
{
  logger.log(1, "\nIC3IAQ::Refinemenent with {} steps\n", cex_.size());
  // counterexample trace must have been populated
  assert(cex_.size());
  // in the original ic3ia: bad_ is abstracted precisely: if there are no transitions, then this is a concrete CEX
  // but this is not the case for quantified properties

  // Recall that cex.back() is an abstract state which might contain conc states outside of bad_ (due to the abstraction being not precise)
  // Let query denote the BMC query of length cex.size() by excluding the constraint cex.back() at step n
  //
  // 1) if query /\ bad_ is sat then return NO_REFINE
  // 2) If unsat, call interpolation on query /\ cex.back(): 
  //    if also unsat (thus refinement), then return REFINE
  //    if sat (thus no refinement) then 
  //       by def of cex.back() (see reconstruct_trace), it is the abstraction of a concrete state in bad_.
  //       pick a concrete state s in cex.back() /\ bad_
  //       refine using interpolants on query /\ s

  // todo we might want to generalize the cube s to a larger set which all intersect bad_ (how?)

  // 1)
  logger.log(3, "Checking BMC query to bad_\n");
  size_t cex_length = cex_.size();
  push_solver_context(); // push query
  for (size_t i = 0; i < cex_length - 1; ++i) {
    register_symbol_mappings(i);
    Term t = unroller_.at_time(cex_[i], i);
    if (i + 1 < cex_length) {
      t = solver_->make_term(And, t, unroller_.at_time(conc_ts_.trans(), i));
    }
    solver_->assert_formula(t);
  }
  solver_->assert_formula(unroller_.at_time(bad_, cex_length-1));
  Result r = solver_->check_sat();
  if (!r.is_sat()){
    // solver_->
  }
  pop_solver_context(); // pop query
  if (r.is_sat()){
    logger.log(3, "Confirmed trace\n");
    return RefineResult::REFINE_NONE;
  }

  // 2)
  // use interpolator to get predicates
  // remember -- need to transfer between solvers
  assert(interpolator_ || external_interpolator_.getSolverEnum() != ExternalInterpolatorEnum::NONE);

  logger.log(3, "Checking BMC query + interpolants to cex.back()");
  TermVec formulae;
  for (size_t i = 0; i < cex_length; ++i) {
    // make sure to_solver_ cache is populated with unrolled symbols
    register_symbol_mappings(i);

    Term t = unroller_.at_time(cex_[i], i);
    if (i + 1 < cex_length) {
      t = solver_->make_term(And, t, unroller_.at_time(conc_ts_.trans(), i));
    }
    formulae.push_back(to_interpolator_.transfer_term(t, BOOL));
  }
  TermVec out_interpolants;
  r = smt::ResultType::UNKNOWN;
  if (external_interpolator_.getSolverEnum() != ExternalInterpolatorEnum::NONE){
    r = external_interpolator_.get_sequence_interpolants(formulae, out_interpolants);
  } else {
    r =
      interpolator_->get_sequence_interpolants(formulae, out_interpolants);
  }

  if (r.is_sat()) {
    logger.log(3, "\t sat\nChecking BMC query + interpolants to concrete state cex.back() /\\ bad_\n");
    // 2b this may not be a real counterexample yet:
    //       pick a concrete state s in cex.back() /\ bad_
    //       refine using interpolants on query /\ s
    push_solver_context();
    logger.log(3, "cex.back(): " + cex_.back()->to_string());
    logger.log(3, "bad_: " + bad_->to_string());
    solver_->assert_formula(bad_);
    solver_->assert_formula(cex_.back());
    // TODO to obtain better predicates, add the invariant that clocks >= 0 

    r = solver_->check_sat();
    assert(r.is_sat());
    // build concrete state cube    
    smt::Term s = solver_->make_term(true);
    for (auto v : ts_.statevars()){
      smt::Term vt = solver_->get_value(v);
      s = solver_->make_term(smt::And, s, solver_->make_term(smt::Equal, v, solver_->get_value(v)));
    }
   

    s = unroller_.at_time(s, cex_length-1);
    pop_solver_context();
    logger.log(3, "conc bad cube: " + s->to_string());
    cex_.pop_back();
    cex_.push_back(s);

    // Now start interpolation again:
    formulae.pop_back();

    formulae.push_back(to_interpolator_.transfer_term(s, BOOL));
    r = smt::ResultType::UNKNOWN;
    if (external_interpolator_.getSolverEnum() != ExternalInterpolatorEnum::NONE){
      r = external_interpolator_.get_sequence_interpolants(formulae, out_interpolants);
    } else {
      r =
        interpolator_->get_sequence_interpolants(formulae, out_interpolants);
    }
    assert(!r.is_sat());
  }

  // record the length of this counterexample
  // important to set it here because it's used in register_symbol_mapping
  // to determine if state variables unrolled to a certain length
  // have already been cached in to_solver_
  longest_cex_length_ = cex_length;

  UnorderedTermSet preds;
  for (auto const&I : out_interpolants) {
    if (!I) {
      std::cout << "null\n";
      assert(
          r.is_unknown());  // should only have null terms if got unknown result
      continue;
    }

    Term solver_I = unroller_.untime(to_solver_.transfer_term(I, BOOL));
    assert(conc_ts_.only_curr(solver_I));
    logger.log(3, "got interpolant: {}", solver_I);
    get_predicates(solver_, solver_I, preds, false, false, true);
  }

  // new predicates
  TermVec fresh_preds;
  for (auto const&p : preds) {
    if (predset_.find(p) == predset_.end()) {
      // unseen predicate
      fresh_preds.push_back(p);
    }
  }

  if (!fresh_preds.size()) {
    logger.log(1, "IC3IA: refinement failed: couldn't find any new predicates");
    return RefineResult::REFINE_FAIL;
  }

  if (options_.random_seed_ > 0) {
    shuffle(fresh_preds.begin(),
            fresh_preds.end(),
            default_random_engine(options_.random_seed_));
  }

  // reduce new predicates
  TermVec red_preds;
  if (options_.ic3ia_reduce_preds_
      && ia_.reduce_predicates(cex_, fresh_preds, red_preds)) {
    // reduction successful
    logger.log(2,
               "reduce predicates successful {}/{}",
               red_preds.size(),
               fresh_preds.size());
    if (red_preds.size() < fresh_preds.size()) {
      fresh_preds.clear();
      fresh_preds.insert(fresh_preds.end(), red_preds.begin(), red_preds.end());
    }
  } else {
    // if enabled should only fail if removed all predicates
    // this can happen when there are uninterpreted functions
    // the unrolling can force incompatible UF interpretations
    // but IC3 (which doesn't unroll) still needs the predicates
    // in this case, just use all the fresh predicates
    assert(!options_.ic3ia_reduce_preds_ || red_preds.size() == 0);
    logger.log(2, "reduce predicates FAILED");
  }

  // add all the new predicates
  for (auto const & p : fresh_preds) {
    bool new_pred = add_predicate(p);
    // expect all predicates to be new (e.g. unseen)
    // they were already filtered above
    assert(new_pred);
  }

  logger.log(1, "{} new predicates added by refinement", fresh_preds.size());

  // able to refine the system to rule out this abstract counterexample
  return RefineResult::REFINE_SUCCESS;
}

bool IC3IAQ::witness(std::vector<smt::UnorderedTermMap> & out)
{
  assert(cex_.size());
  push_solver_context();
  for (size_t i = 0; i < cex_.size(); ++i) {
    Term t = unroller_.at_time(cex_[i], i);
    if (i + 1 < cex_.size()) {
      t = solver_->make_term(And, t, unroller_.at_time(conc_ts_.trans(), i));
    }
    solver_->assert_formula(t);
  }
  Result r = solver_->check_sat();
  assert(r.is_sat());
  for (size_t i = 0; i < cex_.size(); ++i) {
    smt::UnorderedTermMap s;
    for (auto v : conc_ts_.statevars()){
      s[v] = solver_->get_value(unroller_.at_time(v, i));
    }
    for (auto v : conc_ts_.inputvars()){
      s[v] = solver_->get_value(unroller_.at_time(v, i));
    }
    out.push_back(s);
  }
  pop_solver_context();

  return true;
}



}  // namespace pono