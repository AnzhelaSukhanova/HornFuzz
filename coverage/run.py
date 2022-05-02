#!/usr/bin/python

QUERIES = 'clean_seeds'
COVERAGE = 'clean_seeds_coverage'

import os

abs_queries = os.path.join(os.getcwd(), QUERIES)
abs_coverage = os.path.join(os.getcwd(), COVERAGE)

IMAGE = 'spacer-coverage'

docker_cmd = [
   'docker run -it',
   f'-v {abs_queries}:/tests',
   f'-v {abs_coverage}:/coverage',
   IMAGE
]

os.system(' '.join(docker_cmd))
