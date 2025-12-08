#pragma once

#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/term_analysis.h"
#include "smt-switch/utils.h"
#include "smt-switch/term.h"
#include "core/prop.h"

namespace pono {

    /** \brief Returns property with the following quantified formula:
     * ~(P(X) /\ ∀ Y. ∀I. T(X, I, Y) -> ~P(Y))
     * =
     * ~P(X) \/ ∃ Y. ∃I. T(X, I, Y) /\ P(Y)
     * 
     * where P is p.prop().
     * 
     * In mode 0 (static), applies quantifier elimination so the returned property is quantifier-free
     * In mode 1 (dynamic), the above formula is the returned property
     */
Property get_rt_consistency_property(Property & p, const TransitionSystem & ts, RTConsistencyMode mode) {
    if (mode != RTConsistencyMode::STATIC && mode != RTConsistencyMode::DYNAMIC){
        throw PonoException("Unsupported mode for rt-consistency: use 0 or 1.");
    }
    const smt::SmtSolver & solver = p.solver();
    // Map nextstatevar to param
    smt::UnorderedTermMap subst;    

    // state variable to quantified param
    smt::UnorderedTermMap var2param_;
    // quantified param to state var
    smt::UnorderedTermMap param2var_;

    for (const auto & sv : ts.statevars()) {
        const smt::Sort & sort = sv->get_sort();
        smt::Term p = solver->make_param("#" + sv->to_string(), sort);
        var2param_[sv] = p;
        subst[ts.next(sv)] = p;
        param2var_[p] = sv;
    }
    for (const auto & sv : ts.inputvars()) {
        const smt::Sort & sort = sv->get_sort();
        smt::Term p = solver->make_param("#" + sv->to_string(), sort);
        var2param_[sv] = p;
        subst[sv] = p;
        param2var_[p] = sv;
    }
    
    // transXY = T(X, pI, pY)
    smt::Term transXY = solver->substitute(ts.trans(), subst);
    // badX = ~P(X)
    smt::Term badX = solver->make_term(smt::Not, p.prop());
    // T(X, pI, pY) /\ P(pY)
    smt::Term rhs = solver->make_term(smt::And, transXY, solver->substitute(p.prop(), var2param_));

    // rhs = exists pI, pY. T(X, pI, pY) /\ P(pY)
    for (auto pv : param2var_) {
        rhs = solver->make_term(smt::Exists, pv.first, rhs);
    }

    if (mode == RTConsistencyMode::STATIC){
        return Property(p.solver(), 
        // ~P(X) \/ QF(exists pI, pY. T(X, pI, pY) /\ P(pY)))
            p.solver()->make_term(smt::Or,badX, p.solver()->eliminate_quantifiers(rhs)),
            "_rtc_" + p.name()
            );
        ;
    } else {
        // ~P(X) \/ exists pI, pY. T(X, pI, pY) /\ P(pY))
        return Property(p.solver(), 
            solver->make_term(smt::Or, badX, rhs),
            "_rtc_" + p.name()
            );
    }
}
}