MathematicaSSHRemote
====================

A Mathematica package that implements remote kernels launch through tunnelled SSH connections.

Copyright 2018 Hermès Bélusca-Maïto, under the [GPL-2.0+](https://spdx.org/licenses/GPL-2.0+) license.

This package attempts at solving the problem described in the ["remote kernel through SSH"](https://mathematica.stackexchange.com/questions/65953/remote-kernel-through-ssh) discussion,
where the following constraints apply:
- both the local and the remote computer are behind a firewall,
- the SSH connection requires authentication via manual password entering, without using SSH keys,
- the code should be written in Wolfram Language.

The key point is to create an SSH tunnel with remote port forwardings.

This code is inspired from two sources:
- from the [MathematicaSSHKernels](https://github.com/Riebart/MathematicaSSHKernels) package
  (see also the associated discussion: ["Programmatic remote kernel creation via SSH"](http://community.wolfram.com/groups/-/m/t/1394764)),
- and from the [Tunnel](https://github.com/sakra/Tunnel) package by Sascha Kratky (the historical version can be found [here](http://library.wolfram.com/infocenter/Conferences/7250/))
  that was mentioned in the ["Remote Kernel - Error = MLECONNECT"](https://mathematica.stackexchange.com/questions/28274/remote-kernel-error-mleconnect) discussion.


Installation
------------

Download the `SSHRemote.m` file and copy it into `$UserBaseDirectory<>"\\Applications"`.

Alternatively, you can create a sub-directory named `SSHRemote` under `$UserBaseDirectory<>"\\Applications"`
and copy the `SSHRemote.m` file into it. You should then append the `$UserBaseDirectory<>"\\Applications\\SSHRemote"`
directory path to the `$Path` definition in your `$UserBaseDirectory<>"\\Kernel\\init.m"` file.


Usage examples
--------------

See the `examples.nb` notebook for some usage examples.
