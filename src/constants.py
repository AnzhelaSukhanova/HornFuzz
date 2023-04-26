MUT_APPLY_TIME_LIMIT = 10
SEED_SOLVE_TIME_LIMIT_MS = int(2 * 1e3)
MUT_SOLVE_TIME_LIMIT_MS = int(50 * 1e3)
ELDARICA_SOLVE_TIME_LIMIT = 100

MODEL_CHECK_TIME_LIMIT_MS = int(1e3)
ONE_INST_MUT_LIMIT = 100

PROBLEMS_LIMIT = 10
MUT_WEIGHT_UPDATE_RUNS = 10*ONE_INST_MUT_LIMIT

INPUTS_GROUP_NUM = 1
MS_IN_SEC = 1000
SEC_IN_HOUR = 3600
DAY = 24
ROUND_NUM = 5

SEED_DIRS = {'sv-benchmarks-clauses',
             'chc-comp21-benchmarks',
             'spacer-benchmarks'}

DISABLED_SPACER_CORE_PARAMETERS = {'spacer.global',
                                   'spacer.p3.share_invariants',
                                   'spacer.p3.share_lemmas',
                                   'spacer.use_lim_num_gen',
                                   'spacer.reset_pob_queue',
                                   'spacer.simplify_lemmas_post',
                                   'spacer.simplify_lemmas_pre',
                                   'spacer.simplify_pob',
                                   'spacer.use_bg_invs',
                                   'spacer.use_euf_gen',
                                   'spacer.use_lemma_as_cti'}

DISABLED_PARAMETERS = {'xform.array_blast_full',
                       'xform.coalesce_rules',
                       'xform.elim_term_ite',
                       'xform.inline_linear_branch',
                       'xform.instantiate_arrays',
                       'xform.instantiate_arrays.enforce',
                       'xform.instantiate_quantifiers',
                       'xform.quantify_arrays',
                       'xform.transform_arrays'}

ENABLED_SPACER_CORE_PARAMETERS = {'spacer.ctp',
                                  'spacer.elim_aux',
                                  'spacer.eq_prop',
                                  'spacer.gg.concretize',
                                  'spacer.gg.conjecture',
                                  'spacer.gg.subsume',
                                  'spacer.ground_pobs',
                                  'spacer.keep_proxy',
                                  'spacer.mbqi',
                                  'spacer.propagate',
                                  'spacer.reach_dnf',
                                  'spacer.use_array_eq_generalizer',
                                  'spacer.use_derivations',
                                  'spacer.use_inc_clause',
                                  'spacer.use_inductive_generalizer'}

ENABLED_PARAMETERS = {'xform.coi',
                      'xform.compress_unbound',
                      'xform.inline_eager',
                      'xform.inline_linear',
                      'xform.slice',
                      'xform.tail_simplifier_pve'}
