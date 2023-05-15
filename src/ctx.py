import gc
import objgraph

current_ctx = None


def set_ctx(ctx):
    global current_ctx
    current_ctx = ctx


def ensure_current_context_is_deletable():
    global current_ctx

    refs = gc.get_referrers(current_ctx)
    log_entry = ''
    if len(refs) > 1:
        dot_file = open("ctx_tree.png", "w")
        objgraph.show_backrefs([current_ctx],
                               max_depth=7,
                               output=dot_file)
        dot_file.seek(0)
        log_entry = {'context_deletion_error': {'refs': str(refs)}} # 'grapf': dot_file.read()}
        current_ctx.__del__()
    return log_entry