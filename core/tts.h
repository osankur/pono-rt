#pragma once
#include "core/ts.h"
#include "core/rts.h"

namespace pono{

/**
 * @brief Whether to allow arbitrarily long durations in [0,infty) (ArbitraryDurations) or
 * all delays must be exactly 1 (UnitDurations)
*/
enum class TimedAutomatonDelays
{
    ArbitraryDurations,
    UnitDurations
};


/**
 * if Strict, all delays are > 0; if Weak >=0, if GeqOne, then >= 1
*/
enum class TADelayStrictness
{
    Strict,
    Weak,
    GeqOne
};

std::string to_string(TADelayStrictness strictness);

/**
 * @brief In the DelayFirst semantics, a single step is made of a delay + edge.
 * In the DelaySecond semantics, we take an edge first, and delay afterwards
*/
enum class TADelayEdgeOrder {
    DelayFirst,
    DelaySecond
};

/**
 * Relational transition relation encoding timed automata semantics.
 * The encoding is built in two steps: first, from the input VMT file,
 * the transition relation of the discrete steps, as well as the location invariants,
 * and urgent location formulas read. Then, encode_timed_automaton_delays builds
 * the full transition relation including delays, and respecting location invariants and urgency.
 * 
 * There are two possible semantics:
 * - non-compact delays: each transition is either a delay, or a discrete step
 * - compact delays: each transition is a discrete step followed by a delay
 * Both integer and real delay-semantics is possible. This is automatically detected
 * by the sort of clock variables (Real or Int). By default, the sort is Real (e.g. if there no clocks).
 * @see TimedVMTEncoder
*/
class TimedTransitionSystem : public RelationalTransitionSystem {
    public:
    TimedTransitionSystem(const smt::SmtSolver & s, 
        TimedAutomatonDelays delay_type = TimedAutomatonDelays::ArbitraryDurations,
        TADelayEdgeOrder edge_order = TADelayEdgeOrder::DelayFirst,
        TADelayStrictness strictness = TADelayStrictness::Strict
        ) : 
        RelationalTransitionSystem(s),
        solver_(s),
        locinvar_(solver_->make_term(true)),
        urgent_(solver_->make_term(false)),
        encoded_delays_(false),
        has_dummy_init_transitions_(false),
        delay_sort_(s->make_sort(smt::REAL)),
        delay_type_(delay_type),
        delay_edge_order_(edge_order),
        delay_strictness_(strictness),
        invariant_(s->make_term(true))
        {
        }
    static const std::string DELAY_VAR_NAME;
    static const std::string DUMMY_INIT_VAR_NAME;

    TimedAutomatonDelays getDelayType() const {
        return delay_type_;
    }
    const smt::UnorderedTermSet & nonclock_vars() {
        return nonclock_vars_;
    }
    const smt::UnorderedTermSet & clock_vars() {
        return clock_vars_;
    }
    void add_clock_var(smt::Term var){
        clock_vars_.insert(var);
    }
    void add_nonclock_var(smt::Term var){
        nonclock_vars_.insert(var);
    }
    const smt::Term & locinvar(){
        return locinvar_;
    }
    const smt::Term & urgent(){
        return urgent_;
    }

    void add_locinvar(const smt::Term & inv){
        locinvar_ = solver_->make_term(smt::And, locinvar_, inv);
    }
    void add_urgent(const smt::Term & u){
        urgent_ = solver_->make_term(smt::Or, urgent(), u);
    }
    /**
     * Redefine the transition relation by adding delays
     * @pre urgent() only contains nonclock variables
     * @pre locinvar() only contains upper bounds on clocks (when put in negation normal form)
     * @pre invar() does not contain clock variables
    */
    void encode_timed_automaton_delays();


    void constrain_invariant(const smt::Term & constraint);
    const smt::Term invariant();

    protected:
    /**
     * Given trans(C,X, I, C',X'), add a real delay variable, and redefine the trans relation as
     * 
     *    C >= 0 
     * /\ delta >= 0 
     * /\ (urgent -> delta = 0) 
     * /\ locinvar 
     * /\ (trans \/ (C'=C+delta)) 
     * /\ locinvar'
     * 
     * Currently not implemented
    */
    void encode_noncompact_delays();

    /* Add trivial edges on init states. This is necessary for the compact encoding since otherwise we cannot start a run with a delay.
     * trans := trans \/ X=X'/\ C=C' /\ init
     */
    void add_dummy_init_transitions();

    /**
     * Given trans(C,X, I, C',X'), add a real delay variable, and redefine the trans relation as
     * 
     * T(C,X, I, C',X') =
     *    C >= 0 
     * /\ delta >= 0 
     * /\ locinvar(C,X)
     * /\ (urgent -> delta = 0) 
     * /\ (trans(C,X,I,C'-delta,X')
     * /\ locinvar(X',C')
     * 
     * Moreover, to allow delays at the first step, we add a dummy init edge (without guard or reset).
     * @pre locinvar only contains upper bounds on clocks (when put in negation normal form)
    */
    void encode_compact_delays();

    const smt::SmtSolver & solver_;
    smt::UnorderedTermSet nonclock_vars_;
    smt::UnorderedTermSet clock_vars_;
    smt::Term locinvar_;
    smt::Term urgent_;
    smt::Term delta_;
    smt::Sort delay_sort_;
    TimedAutomatonDelays delay_type_;
    TADelayEdgeOrder delay_edge_order_;
    TADelayStrictness delay_strictness_;

    bool encoded_delays_;
    bool has_dummy_init_transitions_;

    private:
    smt::Term invariant_;
};
}