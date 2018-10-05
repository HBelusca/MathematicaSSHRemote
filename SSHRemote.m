(* ::Package:: *)

(* ::Title:: *)
(*SSHRemote package*)


(* ::Subtitle:: *)
(*A Mathematica package that implements remote kernels launch through tunnelled SSH connections.*)


(* ::Subsubtitle:: *)
(*Copyright 2018 Herm\[EGrave]s B\[EAcute]lusca-Ma\[IDoubleDot]to, under the GPL-2.0+ (https://spdx.org/licenses/GPL-2.0+) license.*)


(* ::Text:: *)
(*This package attempts at solving the problem described in https://mathematica.stackexchange.com/questions/65953/remote-kernel-through-ssh ,*)
(*where the following constraints apply:*)
(*- both the local and the remote computer are behind a firewall,*)
(*- the SSH connection requires authentication via manual password entering, without using SSH keys,*)
(*- the code should be written in Wolfram Language.*)
(**)
(*The key point is to create an SSH tunnel with remote port forwardings.*)
(**)
(*This code is inspired from two sources:*)
(*- from the "MathematicaSSHKernels" package, at: https://github.com/Riebart/MathematicaSSHKernels*)
(*  (see also the associated discussion at: http://community.wolfram.com/groups/-/m/t/1394764),*)
(*- and from the "Tunnel" package by Sascha Kratky, at: https://github.com/sakra/Tunnel (the historical version can be found at: http://library.wolfram.com/infocenter/Conferences/7250/)*)
(*  that was mentioned in the following discussion: https://mathematica.stackexchange.com/questions/28274/remote-kernel-error-mleconnect .*)


BeginPackage["SSHRemote`", {"SubKernels`LinkKernels`","SubKernels`RemoteKernels`"}]


(* ::Subsection:: *)
(*Backwards-compatibility*)


If[$VersionNumber<7,
  System`FileNameJoin[names_List]:=ToFileName[Sequence @@ If[names =!= {}, {names[[;; -2]], names[[-1]]}, {names}]];
];
If[$VersionNumber<10,
  System`BooleanQ[expr_]:=MatchQ[expr,True|False];
];
If[$VersionNumber<10.2,
  System`FailureQ[expr_]:=MatchQ[expr,_Failure|$Failed|$Aborted];
];
(* Basic version of StringRiffle[] *)
If[$VersionNumber<10.1,
  StringRiffle[list_List,sep_String]:=StringJoin@Riffle[If[!StringQ[#],ToString[#],#]&/@list,sep];
  StringRiffle[list_List]:=StringRiffle[list," "];
]


(* ::Subsection:: *)
(*Implementation*)


Off[General::shdw]; (* Switch off shadowing warnings for Verbose, Asynchronous and OperatingSystem *)


SSHRemote`SshLaunchRemote::usage=
"SshLaunchRemote[host_String, username_String, cmdTemplate_String, n_Integer, OptionsPattern[]]
Starts n remote kernels via an SSH connection to the specified host and user. The specific remote kernel command is specified via the cmdTemplate parameter; see ?$RemoteCommand for the specific syntax.

The valid options are:
- Multiplexing\[Rule]True|False: Whether or not a multiplexed SSH connection is used when starting n kernels. When a multiplexed SSH connection is used, the login is requested only once, and the remote kernels all share the same SSH connection. The default value is False.
- MultiplexingCommands\[Rule]{startCmd_String, ctlCmd_String}: Custom commands to manipulate the multiplexed SSH connection.
- Verbose\[Rule]True|False: Whether or not diagnostic messages are displayed during connection. The default value is False.
";
SSHRemote`Multiplexing::usage="Multiplexing is an option for SshLaunchRemote[]. Multiplexing\[Rule]True|False: Whether or not a multiplexed SSH connection is used when starting n kernels. When a multiplexed SSH connection is used, the login is requested only once, and the remote kernels all share the same SSH connection. The default value is False.";
SSHRemote`MultiplexingCommands::usage="MultiplexingCommands is an option for SshLaunchRemote[]. MultiplexingCommands\[Rule]{startCmd_String, ctlCmd_String}: Custom commands to manipulate the multiplexed SSH connection.";
SSHRemote`Verbose::usage="Verbose is an option for SshLaunchRemote[]. Verbose\[Rule]True|False: Whether or not diagnostic messages are displayed during connection. The default value is False.";


SSHRemote`AdjustCommandLine::usage=
"AdjustCommandLine[cmdLine_String, OptionsPattern[]]
Adjusts the specified command line for a specific operating system.

The valid options are:
- Asynchronous\[Rule]True|False: Whether or not support for asynchronous command should be added. The default value is False.
- OperatingSystem\[Rule]\"Windows\"|\"WSL\"|\"WSLNew\"|\"Unix\"|\"MacOSX\": The choice of operating system: \"Windows\", \"Unix\", or \"MacOSX\" for one of these operating systems.
  The options \"WSL\" or \"WSLNew\" correspond to the 'Windows Subsystem for Linux', and are only valid on Windows 10 x64 version 1607 and above.
  See https://docs.microsoft.com/en-us/windows/wsl/about , https://docs.microsoft.com/en-us/windows/wsl/faq , and https://docs.microsoft.com/en-us/windows/wsl/install-win10 for more details.
  The default value is given by the value of $OperatingSystem.
";
SSHRemote`Asynchronous::usage="Asynchronous is an option for AdjustCommandLine[]. Asynchronous\[Rule]True|False: Whether or not support for asynchronous command should be added. The default value is False.";
SSHRemote`OperatingSystem::usage="OperatingSystem is an option for AdjustCommandLine[]. OperatingSystem\[Rule]\"Windows\"|\"WSL\"|\"WSLNew\"|\"Unix\"|\"MacOSX\": The choice of operating system: \"Windows\", \"Unix\", or \"MacOSX\" for one of these operating systems.
The options \"WSL\" or \"WSLNew\" correspond to the 'Windows Subsystem for Linux', and are only valid on Windows 10 x64 version 1607 and above.
See https://docs.microsoft.com/en-us/windows/wsl/about , https://docs.microsoft.com/en-us/windows/wsl/faq , and https://docs.microsoft.com/en-us/windows/wsl/install-win10 for more details.
The default value is given by the value of $OperatingSystem.";


On[General::shdw]; (* Restore shadowing warnings *)


Begin["`Private`"]


(* Standard paths to Java and MathSSH *)
$JavaCommand = FileNameJoin[{$InstallationDirectory,"SystemFiles","Java",$SystemID,"bin","java"}];
$WolframSSH = $MathSSH = FileNameJoin[{$InstallationDirectory,"SystemFiles","Java","WolframSSH.jar"}];


cmdLineRun[cmdTemplate_String, verbose_?BooleanQ, msgTemplate_String:"", strRepRules:{(_String->_) ...}, strFormExprs_List]:=
Module[{cmdLine},
  (* Build the full command line *)
  cmdLine=StringReplace[cmdTemplate, {"`java`"->$JavaCommand, "`mathssh`"->$MathSSH, "`wolframssh`"->$WolframSSH, Sequence@@strRepRules}];
  cmdLine=StringForm[cmdLine, Sequence@@strFormExprs];
  If[verbose, Print@StringForm[msgTemplate,cmdLine]];

  (* Start it *)
  {Run[cmdLine],cmdLine}
];


Options[SshLaunchRemote]={SSHRemote`Multiplexing->False, SSHRemote`MultiplexingCommands->{(* Start *)"",(* Control commands *)""}, Verbose->False};

SyntaxInformation[SshLaunchRemote]={"ArgumentsPattern"->{_,_,__,OptionsPattern[]}, "OptionNames"->(*optionNames[SshLaunchRemote]*){"Multiplexing","MultiplexingCommands","Verbose"}};

SshLaunchRemote[host_String, username_String, cmdTemplate_String, n_Integer, OptionsPattern[]]:=
Module[{multiplex,multiplexCmds,verbose,java,wolframssh,mathssh,links,cmdLine,code},
  {multiplex,multiplexCmds,verbose}=OptionValue@{SSHRemote`Multiplexing,SSHRemote`MultiplexingCommands,Verbose};
  If[!BooleanQ[multiplex],Message[General::opttf,SshLaunchRemote,multiplex];Abort[]];
  If[!MatchQ[multiplexCmds,{_String,_String}],Message[General::irule,multiplexCmds];Abort[]];(*General::optrs*)
  If[!BooleanQ[verbose],Message[General::opttf,SshLaunchRemote,verbose];Abort[]];
  If[n<=0,Print["The number of kernels must be a positive integer!"];Abort[];];

  If[multiplex,Print["SSH with Multiplexing"],Print["SSH with NO Multiplexing"]];

  (* Create new connection links *)
  links=Table[LinkCreate[LinkProtocol->"TCPIP"],n];
  links=SubKernels`Protected`deleteFailed[links,SshLaunchRemote];

  (* Start SSH multiplexing mode if needed *)
  If[multiplex&&multiplexCmds[[1]]=!="",
    {code,cmdLine}=cmdLineRun[multiplexCmds[[1]], verbose, "SSH multiplexing mode command line: '`1`'", {(*"`ports`"\[Rule]sshPorts*)}, {host,username,username}];
    If[code!=0,Print["Failed to start SSH multiplexing mode on ",host," , falling back to regular connection!"];Message[SubKernels`RemoteKernels`LaunchRemote::rsh,cmdLine,code];multiplex=False;];
  ];

  Module[{link=#,linkPorts,sshPorts,linkName},
    (* Parse the TCPIP link names and extract the link ports *)
    linkPorts=Function[{link},link[[1]]//(Reverse[StringSplit[#,"@"]]&)/@StringSplit[#,","]&]@link;

    (* Set up remote port forwardings for kernel main link. Note that no local port forwardings are required for compute kernels. *)
    sshPorts=StringRiffle@(StringRiffle[Join[{"-R 127.0.0.1",#[[2]]},#],":"]&/@linkPorts);

    (* Build the correct forwarded link name *)
    linkName=StringRiffle[(#<>"@127.0.0.1")&/@linkPorts[[All,2]],","];

    (* Set port forwarding in SSH multiplexing mode if needed *)
    If[multiplex,
      {code,cmdLine}=cmdLineRun[multiplexCmds[[2]], verbose, "SSH multiplexing mode port forwarding command line: '`1`'", {"`ctlcmd`"->"forward","`params`"->sshPorts}, {host,username,username}];
      If[code!=0,Print["Failed to set SSH multiplexing mode port forwarding on ",host," , falling back to regular connection!"];Message[SubKernels`RemoteKernels`LaunchRemote::rsh,cmdLine,code];multiplex=False;];
    ];

    (* Build the full command line and start it *)
    {code,cmdLine}=cmdLineRun[cmdTemplate, verbose, "Full command line: '`1`'", {"`ports`"->If[multiplex,"",sshPorts],"`linkname`"->linkName,"`ipaddress`"->"127.0.0.1"}, {host,linkName,username,"-LinkProtocol TCPIP"}];
    If[code!=0,Print["Failed to start SSH remote kernel on ",host," !"];Message[SubKernels`RemoteKernels`LaunchRemote::rsh,cmdLine,code];LinkClose[link];];
  ]&/@links;

  (* Stop port forwarding in SSH multiplexing mode if needed *)
  If[multiplex,
    {code,cmdLine}=cmdLineRun[multiplexCmds[[2]], verbose, "SSH multiplexing mode port forwarding command line: '`1`'", {"`ctlcmd`"->"stop","`params`"->""}, {host,username,username}];
    If[code!=0,Print["Failed to set SSH multiplexing mode port forwarding on ",host," , falling back to regular connection!"];Message[SubKernels`RemoteKernels`LaunchRemote::rsh,cmdLine,code];multiplex=False;];
  ];

  (* Attempt to connect to the kernels. If it succeeds, we don't need to close the links; they will be automatically closed when the kernels are terminated using CloseKernels[]. *)
  Module[{link=#,kernel},kernel=LaunchKernels[link];If[FailureQ[kernel],Print["Failed to start a remote kernel on ",host," !"];LinkClose[link];];kernel]&/@links
];

SshLaunchRemote[host_String,username_String,cmdTemplate_String,opts:OptionsPattern[]]:=SshLaunchRemote[host,username,cmdTemplate,1,opts];


Options[AdjustCommandLine]={SSHRemote`Asynchronous->False, SSHRemote`OperatingSystem->$OperatingSystem};

SyntaxInformation[AdjustCommandLine]={"ArgumentsPattern"->{_,OptionsPattern[]}, "OptionNames"->(*optionNames[AdjustCommandLine]*){"Asynchronous","OperatingSystem"}};

AdjustCommandLine[cmdLine_String, OptionsPattern[]]:=
Module[{async,os},
  {async,os}=OptionValue@{SSHRemote`Asynchronous,SSHRemote`OperatingSystem};
  If[!BooleanQ[async],Message[General::opttf,AdjustCommandLine,async];Abort[]];
  If[!MatchQ[os,"Windows"|"WSL"|"WSLNew"|"Unix"|"MacOSX"], Message[General::optvg,AdjustCommandLine,os,"Windows"|"WSL"|"WSLNew"|"Unix"|"MacOSX"]; Abort[]];

  Switch[os,
    "Windows",
      If[async,"start ",""]<>cmdLine
    ,
    "WSL",
      If[async,"start ",""]<>"bash -c "<>ToString[cmdLine,InputForm]
    ,
    "WSLNew",
      If[async,"start ",""]<>(*"wsl -e "*)"wsl "<>cmdLine
    ,
    _ (* "Unix" | "MacOSX" *),
      cmdLine<>If[async," &",""]
  ]
];


End[]


EndPackage[]
