import json
import logging

import z3


def global_ctx_access_exception():
    raise Exception('Global z3 context access')


def z3_context_safe_del(self):
    if self.ctx is None:
        logging.error(json.dumps({'context_deletion_error': 'context already deleted'}))
        return
    z3.Z3_del_context(self.ctx)
    self.ctx = None
    self.eh = None


def z3_context_safe_ref(self):
    if self.ctx is None:
        raise Exception('Context deleted')
    return self.ctx


def fixed_solver_for(logic, ctx=None, logFile=None):
    ctx = z3.get_ctx(ctx)
    logic = z3.to_symbol(logic, ctx=ctx)
    return z3.Solver(z3.Z3_mk_solver_for_logic(ctx.ref(), logic), ctx, logFile)


z3.Context.__del__ = z3_context_safe_del
z3.Context.ref = z3_context_safe_ref
z3.SolverFor.__code__ = fixed_solver_for.__code__
z3.main_ctx.__code__ = global_ctx_access_exception.__code__
