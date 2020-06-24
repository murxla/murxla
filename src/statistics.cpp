#include "statistics.hpp"

namespace smtmbt {
namespace statistics {

std::ostream&
operator<<(std::ostream& out, Action action)
{
  switch (action)
  {
    case ACTION_NEW: out << "ACTION_NEW"; break;
    case ACTION_DELETE: out << "ACTION_DELETE"; break;
    case ACTION_MK_SORT: out << "ACTION_MK_SORT"; break;
    case ACTION_MK_VALUE: out << "ACTION_MK_VALUE"; break;
    case ACTION_MK_CONST: out << "ACTION_MK_CONST"; break;
    case ACTION_MK_TERM: out << "ACTION_MK_TERM"; break;
    case ACTION_ASSERT_FORMULA: out << "ACTION_ASSERT_FORMULA"; break;
    case ACTION_GET_UNSAT_ASSUMPTIONS:
      out << "ACTION_GET_UNSAT_ASSUMPTIONS";
      break;
    case ACTION_GET_VALUE: out << "ACTION_GET_VALUE"; break;
    case ACTION_PRINT_MODEL: out << "ACTION_PRINT_MODEL"; break;
    case ACTION_CHECK_SAT: out << "ACTION_CHECK_SAT"; break;
    case ACTION_CHECK_SAT_ASSUMING: out << "ACTION_CHECK_SAT_ASSUMING"; break;
    case ACTION_PUSH: out << "ACTION_PUSH"; break;
    case ACTION_POP: out << "ACTION_POP"; break;
    case ACTION_RESET_ASSERTIONS: out << "ACTION_RESET_ASSERTIONS"; break;
    case ACTION_SET_OPTION: out << "ACTION_SET_OPTION"; break;
    case ACTION_T: out << "ACTION_T"; break;
    case ACTION_T_CREATE_INPUTS: out << "ACTION_T_CREATE_INPUTS"; break;

    /* Boolector specific actions */
    case ACTION_BTOR_OPT_ITERATOR: out << "ACTION_BTOR_OPT_ITERATOR"; break;
    case ACTION_BTOR_BV_ASSIGNMENT: out << "ACTION_BTOR_BV_ASSIGNMENT"; break;
    case ACTION_BTOR_CLONE: out << "ACTION_BTOR_CLONE"; break;
    case ACTION_BTOR_FAILED: out << "ACTION_BTOR_FAILED"; break;
    case ACTION_BTOR_FIXATE_ASSUMPTIONS:
      out << "ACTION_BTOR_FIXATE_ASSUMPTIONS";
      break;
    case ACTION_BTOR_RESET_ASSUMPTIONS:
      out << "ACTION_BTOR_RESET_ASSUMPTIONS";
      break;
    case ACTION_BTOR_RELEASE_ALL: out << "ACTION_BTOR_RELEASE_ALL"; break;
    case ACTION_BTOR_SIMPLIFY: out << "ACTION_BTOR_SIMPLIFY"; break;
    case ACTION_BTOR_SET_SAT_SOLVER: out << "ACTION_BTOR_SET_SAT_SOLVER"; break;
    case ACTION_BTOR_SET_SYMBOL: out << "ACTION_BTOR_SET_SYMBOL"; break;

    /* CVC4 specific actions */
    case ACTION_CVC4_CHECK_ENTAILED: out << "ACTION_CVC4_CHECK_ENTAILED"; break;
    case ACTION_CVC4_SIMPLIFY: out << "ACTION_CVC4_SIMPLIFY"; break;

    default: assert(action == NUM_ACTIONS);
  }

  return out;
}

std::ostream&
operator<<(std::ostream& out, State state)
{
  std::string name;
  switch (state)
  {
    case STATE_NEW: out << "STATE_NEW"; break;
    case STATE_OPT: out << "STATE_OPT"; break;
    case STATE_DELETE: out << "STATE_DELETE"; break;
    case STATE_FINAL: out << "STATE_FINAL"; break;
    case STATE_CREATE_INPUTS: out << "STATE_CREATE_INPUTS"; break;
    case STATE_CREATE_TERMS: out << "STATE_CREATE_TERMS"; break;
    case STATE_ASSERT: out << "STATE_ASSERT"; break;
    case STATE_MODEL: out << "STATE_MODEL"; break;
    case STATE_CHECK_SAT: out << "STATE_CHECK_SAT"; break;
    case STATE_PUSH_POP: out << "STATE_PUSH_POP"; break;

    /* Solver specific states */

    /* Boolector */
    case STATE_BTOR_FIX_RESET_ASSUMPTIONS:
      out << "STATE_BTOR_FIX_RESET_ASSUMPTIONS";
      break;

      /* CVC4 */

    default: assert(state == NUM_STATES);
  }
  return out;
}

void
Statistics::print() const
{
  std::cout << std::endl;

  uint64_t sum = 0;

  std::cout << "States:" << std::endl;
  for (uint32_t i = 0; i < State::NUM_STATES; ++i)
  {
    std::cout << "  " << static_cast<State>(i) << ": " << d_states[i]
              << std::endl;
    sum += d_states[i];
  }
  std::cout << "  Total: " << sum << std::endl;

  sum = 0;
  std::cout << "Actions:" << std::endl;
  for (uint32_t i = 0; i < Action::NUM_ACTIONS; ++i)
  {
    std::cout << "  " << static_cast<Action>(i) << ": " << d_actions[i] << " ("
              << d_actions_ok[i] << ")" << std::endl;
    sum += d_actions[i];
  }
  std::cout << "  Total: " << sum << std::endl;

  sum = 0;
  std::cout << "Results:" << std::endl;
  for (uint32_t i = 0; i < 3; ++i)
  {
    std::cout << "  " << static_cast<Solver::Result>(i) << ": " << d_results[i]
              << std::endl;
    sum += d_results[i];
  }
  std::cout << "  Total: " << sum << std::endl;

  sum = 0;
  std::cout << "Ops:" << std::endl;
  for (uint32_t i = 0; i < OpKind::OP_ALL; ++i)
  {
    std::cout << "  " << static_cast<OpKind>(i) << ": " << d_ops[i]
              << std::endl;
    sum += d_ops[i];
  }
  std::cout << "  Total: " << sum << std::endl;
}

}  // namespace statistics
}  // namespace smtmbt
