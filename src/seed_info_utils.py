import json
import os
import re
import os.path

SEED_INFO_FILE_LIMIT = 100
seed_info_path = 'seed_info'


def _load_seed_info(descriptor):
    if os.path.exists(descriptor['path']):
        with open(descriptor['path']) as f:
            return json.load(f)
    return {}


def _write_seed_info(data, descriptor):
    with open(descriptor['path'], 'w') as f:
        json.dump(data, f, indent=2)


def build_seed_info_index():
    if not os.path.exists(seed_info_path):
        os.mkdir(seed_info_path)
    all_files = [os.path.join(seed_info_path, it) for it in os.listdir(seed_info_path)]
    seed_info_files = [it for it in all_files if os.path.isfile(it) and re.fullmatch('.*/\\d+\\.json', it)]
    index = {}
    for file in seed_info_files:
        file_idx = int(file.split('/')[-1].split('.')[0])
        descriptor = {'id': file_idx, 'path': file}
        data = _load_seed_info(descriptor)
        for seed in data.keys():
            index[seed] = descriptor
    return index


def map_seeds_ordered(seeds: dict, index, general_stats, f):
    reverse_index = {}
    for seed, descriptor in index.items():
        seed_group = reverse_index.setdefault(descriptor['id'], {'descriptor': descriptor, 'seeds': set()})
        seed_group['seeds'].add(seed)

    for seed_info_group in reverse_index.values():
        group_seeds = seed_info_group['seeds']
        seeds_for_apply = group_seeds & set(seeds.keys())
        if not seeds_for_apply:
            continue
        seed_info = _load_seed_info(seed_info_group['descriptor'])
        for seed in seeds_for_apply:
            args = seeds[seed]
            args['seed_info'] = seed_info[seed]
            args['general_stats'] = general_stats
            yield f(**args)


def store_seed_info(seed_info, index):
    new_seed_info = {seed: data for seed, data in seed_info.items() if seed not in index}
    if not new_seed_info:
        return
    last_descriptor = {'id': 0, 'path': os.path.join(seed_info_path, '0.json')}
    for descriptor in index.values():
        if descriptor['id'] > last_descriptor['id']:
            last_descriptor = descriptor
    last_descriptor_data = _load_seed_info(last_descriptor)
    new_seed_info_lst = list(new_seed_info.items())
    chunks = []
    first_chunk_size = SEED_INFO_FILE_LIMIT - len(last_descriptor_data)
    chunks.append(list(last_descriptor_data.items()) + new_seed_info_lst[:first_chunk_size])
    new_seed_info_lst = new_seed_info_lst[first_chunk_size:]
    while new_seed_info_lst:
        chunks.append(new_seed_info_lst[:SEED_INFO_FILE_LIMIT])
        new_seed_info_lst = new_seed_info_lst[SEED_INFO_FILE_LIMIT:]

    descriptors = [last_descriptor]
    while len(descriptors) < len(chunks):
        did = descriptors[-1]['id'] + 1
        path = os.path.join(seed_info_path, '{}.json'.format(did))
        descriptors.append({'id': did, 'path': path})
    assert len(descriptors) == len(chunks)
    for data, descriptor in zip(chunks, descriptors):
        dict_data = dict(data)
        _write_seed_info(dict_data, descriptor)
        for seed in dict_data.keys():
            index[seed] = descriptor
