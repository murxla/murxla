class TermData
{
  size_t ref;
}

template <T, TT, TTT>
class SolverManager
{
  void set_solver(T *s) { d_solver = s; }

  T *get_solver() {}

  void add_term(TT term) {}

  TT *pick_term(Theory theory) {}

  void add_sort(TTT sort) {}

  TTT *pick_sort(Theory theory) {}

 private:
  T *d_solver;

  std::unordered_map<TTT, std::unordered_map<TT, TermData>> d_terms;
}

class Action
{
 public:
  virtual void run() = 0;
}

class BtorAction : public Action
{
  BtorAction(BtorSolverManager *smgr) : d_smgr(smgr);

 private:
  BtorSolverManager *d_smgr;
}

class BtorNewAction : public BtorAction
{
  void run() override
  {
    Trace() << ...;
	  Btor *slv = boolector_new();
    d_smgr->set_solver(slv);
    Trace() << ...
  }
}

class BtorDeleteAction : public Action
{
  void run() { boolector_delete(d_smgr->get_solver()); }
}

class State
{
  void add_action(Action *a, uint32_t weight, State *next);
  State *pick_action();
};

class FSM
{
	void next()
	{
		State* next_state = d_cur->pick_action();
		if (next_state != d_cur)
		{
			d_cur = next_state;
		}
	};

	bool done() {};

 private:
//	State *d_init;
	State *d_cur;
	State *d_final;
}

State *
init_fsm_btor()
{
	SolverManager<Btor, BoolectorNode *, BoolectorSort> *mgr = new SolverManager<>();

  State state_new = new State();
  State state_delete = new State();

  state_new->add_action(new BtorNewAction(mgr), 1000, state_delete);
  state_delete->add_action(new BtorDeleteAction(mgr), 1000, nullptr);

  return state_new;
}
