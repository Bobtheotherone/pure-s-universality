Get["implementation/wolfram/PureS.wl"];
t=PureSEncode[{{1},{}},{1,0,1}];
seen={PureSDecode[t]};
Do[t=PureSStep[t]; data=PureSInspect[t]; If[TrueQ[data[[2]]],AppendTo[seen,data[[1]]]],{6}];
Print[seen];
If[seen=!={{1,0,1},{0,1,1},{1,1}},Quit[1]];
If[!TrueQ[PureSHalt[PureSEncode[{{}},{}]]],Quit[2]];
Print["PASS cyclic samples and initially empty input"];Quit[0];
