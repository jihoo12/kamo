#!/usr/bin/env python3
"""Check the exported acyclic text grammar and count its expansion without expanding.
This checks representation/size, not typing or reduction correctness.
"""
import argparse
from array import array
import hashlib
import json


def analyze(path):
    lengths, offsets, edges, opens = (array('Q') for _ in range(4))
    deltas, minima = array('q'), array('q')
    leaves = {}
    offsets.append(0)
    digest = hashlib.sha256()
    root = expected = None
    with open(path, 'rb') as stream:
        header = stream.readline()
        digest.update(header)
        complete = header == b'kamo-normal-dag-v1\n'
        if not complete and header != b'kamo-normal-dag-prefix-v1-INCOMPLETE\n':
            raise ValueError('unrecognized DAG header')
        for line in stream:
            digest.update(line)
            fields = line.split(maxsplit=2)
            if fields[0] == b'root':
                parts = line.split()
                if len(parts) != 4 or parts[2] != b'expanded-bytes':
                    raise ValueError('invalid root line')
                root, expected = int(parts[1]), int(parts[3])
                if stream.read(1):
                    raise ValueError('data after root')
                break
            index = int(fields[0])
            if index != len(lengths):
                raise ValueError('nonsequential node ID')
            if fields[1] == b'text':
                value = json.loads(fields[2]).encode('utf-8')
                leaves[index] = value
                length = len(value)
                delta = minimum = 0
                for byte in value:
                    delta += (byte == 40) - (byte == 41)
                    minimum = min(minimum, delta)
                opening = value.count(b'(')
            elif fields[1] == b'concat':
                length = delta = minimum = opening = 0
                for child in fields[2].split() if len(fields) == 3 else []:
                    child = int(child)
                    if child >= index or child < 0:
                        raise ValueError('non-acyclic reference')
                    edges.append(child)
                    length += lengths[child]
                    opening += opens[child]
                    minimum = min(minimum, delta + minima[child])
                    delta += deltas[child]
            else:
                raise ValueError('unknown node kind')
            lengths.append(length)
            offsets.append(len(edges))
            opens.append(opening)
            deltas.append(delta)
            minima.append(minimum)
    if root is None or root >= len(lengths) or lengths[root] != expected:
        raise ValueError('missing root or incorrect expanded length')
    if complete and (deltas[root] or minima[root] < 0):
        raise ValueError('complete output is not parenthesis balanced')
    counts = array('Q', [0]) * len(lengths)
    counts[root] = 1
    for parent in range(len(lengths) - 1, -1, -1):
        for pos in range(offsets[parent], offsets[parent + 1]):
            child = edges[pos]
            counts[child] += counts[parent]
    def prefix(index, maximum=100):
        out = bytearray()
        pending = [index]
        while pending and len(out) < maximum:
            node = pending.pop()
            if node in leaves:
                out.extend(leaves[node][:maximum - len(out)])
            else:
                pending.extend(reversed(edges[offsets[node]:offsets[node + 1]]))
        return out.decode('utf-8')
    candidates = (i for i, count in enumerate(counts)
                  if count > 1 and lengths[i] >= 4096 and deltas[i] == 0 and minima[i] >= 0)
    import heapq
    largest = heapq.nlargest(12, candidates, key=lambda i: lengths[i])
    report = {
        'status': 'complete' if complete else 'INCOMPLETE PREFIX',
        'sha256': digest.hexdigest(),
        'expanded_bytes': expected,
        'expanded_lists': opens[root],
        'dag_nodes': len(lengths),
        'reachable_nodes': sum(count != 0 for count in counts),
        'edges': len(edges),
        'unfinished_parentheses': deltas[root],
        'largest_repeated_fragments': [
            {'node': i, 'bytes': lengths[i], 'occurrences': counts[i], 'prefix': prefix(i)}
            for i in largest
        ],
        'note': 'Nested fragments overlap; do not sum their byte contributions.'
    }
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('path')
    analyze(parser.parse_args().path)
