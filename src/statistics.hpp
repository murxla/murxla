#ifndef __SMTMBT__STATISTICS_H
#define __SMTMBT__STATISTICS_H

#include "op.hpp"
#include "solver.hpp"

namespace smtmbt {

namespace statistics {

enum Action
{
  ACTION_NEW,
  ACTION_DELETE,
  ACTION_MK_SORT,
  ACTION_MK_VALUE,
  ACTION_MK_CONST,
  ACTION_MK_TERM,
  ACTION_ASSERT_FORMULA,
  ACTION_GET_UNSAT_ASSUMPTIONS,
  ACTION_GET_VALUE,
  ACTION_PRINT_MODEL,
  ACTION_CHECK_SAT,
  ACTION_CHECK_SAT_ASSUMING,
  ACTION_PUSH,
  ACTION_POP,
  ACTION_RESET_ASSERTIONS,
  ACTION_SET_OPTION,
  ACTION_T,
  ACTION_T_CREATE_INPUTS,
  ACTION_T_CREATE_SORTS,
  ACTION_T_MODEL,

  /* Boolector specific actions */
  ACTION_BTOR_OPT_ITERATOR,
  ACTION_BTOR_BV_ASSIGNMENT,
  ACTION_BTOR_CLONE,
  ACTION_BTOR_FAILED,
  ACTION_BTOR_FIXATE_ASSUMPTIONS,
  ACTION_BTOR_RESET_ASSUMPTIONS,
  ACTION_BTOR_RELEASE_ALL,
  ACTION_BTOR_SIMPLIFY,
  ACTION_BTOR_SET_SAT_SOLVER,
  ACTION_BTOR_SET_SYMBOL,

  /* CVC4 specific actions */
  ACTION_CVC4_CHECK_ENTAILED,
  ACTION_CVC4_SIMPLIFY,

  NUM_ACTIONS
};

std::ostream& operator<<(std::ostream& out, Action action);

const std::unordered_map<std::string, Action> g_action_str_to_enum = {
    {"new", ACTION_NEW},
    {"delete", ACTION_DELETE},
    {"mk-sort", ACTION_MK_SORT},
    {"mk-value", ACTION_MK_VALUE},
    {"mk-const", ACTION_MK_CONST},
    {"mk-term", ACTION_MK_TERM},
    {"assert-formula", ACTION_ASSERT_FORMULA},
    {"get-unsat-assumptions", ACTION_GET_UNSAT_ASSUMPTIONS},
    {"get-value", ACTION_GET_VALUE},
    {"print-model", ACTION_PRINT_MODEL},
    {"check-sat", ACTION_CHECK_SAT},
    {"check-sat-assuming", ACTION_CHECK_SAT_ASSUMING},
    {"push", ACTION_PUSH},
    {"pop", ACTION_POP},
    {"reset-assertions", ACTION_RESET_ASSERTIONS},
    {"set-option", ACTION_SET_OPTION},

    /* default for all transitions */
    {"", ACTION_T},
    {"t_inputs", ACTION_T_CREATE_INPUTS},
    {"t_sorts", ACTION_T_CREATE_SORTS},
    {"t_model", ACTION_T_MODEL},

    /* Boolector specific actions */
    {"btor-opt-iterator", ACTION_BTOR_OPT_ITERATOR},
    {"btor-bv-assignment", ACTION_BTOR_BV_ASSIGNMENT},
    {"btor-clone", ACTION_BTOR_CLONE},
    {"btor-failed", ACTION_BTOR_FAILED},
    {"btor-fixate-assumptions", ACTION_BTOR_FIXATE_ASSUMPTIONS},
    {"btor-reset-assumptions", ACTION_BTOR_RESET_ASSUMPTIONS},
    {"btor-release-all", ACTION_BTOR_RELEASE_ALL},
    {"btor-simplify", ACTION_BTOR_SIMPLIFY},
    {"btor-set-sat-solver", ACTION_BTOR_SET_SAT_SOLVER},
    {"btor-set-symbol", ACTION_BTOR_SET_SYMBOL},

    /* CVC4 specific actions */
    {"cvc4-check-entailed", ACTION_CVC4_CHECK_ENTAILED},
    {"cvc4-simplify", ACTION_CVC4_SIMPLIFY},
};

enum State
{
  STATE_NEW,
  STATE_OPT,
  STATE_DELETE,
  STATE_FINAL,
  STATE_CREATE_SORTS,
  STATE_CREATE_INPUTS,
  STATE_CREATE_TERMS,
  STATE_ASSERT,
  STATE_MODEL,
  STATE_CHECK_SAT,
  STATE_PUSH_POP,

  /* Boolector */
  STATE_BTOR_FIX_RESET_ASSUMPTIONS,

  NUM_STATES
};

const std::unordered_map<std::string, State> g_state_str_to_enum = {
    {"new", STATE_NEW},
    {"opt", STATE_OPT},
    {"delete", STATE_DELETE},
    {"final", STATE_FINAL},
    {"create_sorts", STATE_CREATE_SORTS},
    {"create_inputs", STATE_CREATE_INPUTS},
    {"create_terms", STATE_CREATE_TERMS},
    {"assert", STATE_ASSERT},
    {"model", STATE_MODEL},
    {"check_sat", STATE_CHECK_SAT},
    {"push_pop", STATE_PUSH_POP},

    {"btor-fix-reset-assumptions", STATE_BTOR_FIX_RESET_ASSUMPTIONS},
};

std::ostream& operator<<(std::ostream& out, State state);

struct Statistics
{
  uint64_t d_results[3];
  uint64_t d_ops[OpKind::OP_ALL];
  uint64_t d_states[State::NUM_STATES];
  uint64_t d_actions[Action::NUM_ACTIONS];
  uint64_t d_actions_ok[Action::NUM_ACTIONS];

  void print() const;
};

}  // namespace statistics
}  // namespace smtmbt
#endif
