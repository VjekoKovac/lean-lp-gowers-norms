#!/usr/bin/python3
"""Run Lake's bwrap with networking isolated by the outer user namespace.

The launcher creates a fresh network namespace with no external interfaces or
routes. Retaining that empty namespace avoids a blocked NETLINK_ROUTE call
used for bringing up loopback inside another nested bwrap network namespace.
"""
import os
import sys


def main():
    with open('/run/comparator-namespace', encoding='ascii') as record:
        expected, original = record.read().splitlines()
    actual = os.readlink('/proc/self/ns/net')
    if actual != expected or actual == original:
        sys.exit('missing outer offline network namespace')
    with open('/proc/net/dev', encoding='ascii') as devices:
        interfaces = [line.split(':')[0].strip() for line in devices if ':' in line]
    with open('/proc/net/route', encoding='ascii') as routes:
        if interfaces != ['lo'] or len(routes.readlines()) > 1:
            sys.exit('unexpected network access in the outer namespace')
    args = sys.argv[1:]
    if '--unshare-all' not in args:
        sys.exit('unexpected comparator sandbox arguments')
    args.insert(args.index('--unshare-all') + 1, '--share-net')
    os.execv('/usr/bin/bwrap', ['bwrap', *args])


if __name__ == '__main__':
    main()
