BeginPackage["UniformPureS`"];
PureSEncode::usage="PureSEncode[appendants,input] constructs a binary cyclic tag seed.";
PureSInspect::usage="PureSInspect[term] returns the live word, parity, next address and halt flag for a valid binary encoding.";
PureSStep::usage="PureSStep[term] contracts one selected native occurrence and fixes a normal term.";
PureSHalt::usage="PureSHalt[term] detects a stable empty binary queue.";
PureSDecode::usage="PureSDecode[term] extracts the live word.";
Begin["`Private`"];
pair[x_,y_]:=ap[ap[s,x],y];
box[x_]:=pair[s,x];
tag[0]=s; tag[1]=ap[s,s];
word[w_List]:=Fold[Function[{t,b},ap[pair[s,tag[b]],t]],s,Reverse[w]];
arm[v_]:=ap[pair[s,s],v];
slot[w_]:=pair[arm[s],arm[box[word[w]]]];
list[x_List]:=Fold[Function[{t,v},pair[v,t]],s,Reverse[x]];
PureSEncode[p_List,w_List]/;Length[p]>0:=Module[{f,a,x},f=box[list[slot/@p]];
  a=ap[s,f];x=pair[a,a];pair[box[word[w]],ap[x,x]]];
at[t_,{}]:=t; at[t_,p_List]:=Extract[t,p];
degree[t_]:=Module[{n=0,v=t},While[Head[v]===ap&&n<5,n++;v=v[[1]]];n];
red[t_]:=MatchQ[t,ap[ap[ap[s,_],_],_]];
act[ap[ap[ap[s,x_],y_],z_]]:=ap[ap[x,z],ap[y,z]];
assert[ok_]:=If[!TrueQ[ok],Throw[$Failed,bad]];
bit[v_]:=Which[v===s,0,v===ap[s,s],1,True,Throw[$Failed,bad]];
status[v_]:=Which[Head[v]===ap&&v[[1]]===pair[s,s],0,degree[v]===2,1,True,Throw[$Failed,bad]];
PureSInspect[t_]:=Catch[Module[{live={},first=False,last=False,spent=0,fired=0,free=False,rail,lp,sp,za,oa,st,
      scanWord,front,stable,selected,z,v,q,halt},
  scanWord[p_]:=Module[{a=p,u},
    assert[MatchQ[at[t,a],ap[ap[s,s],_]]];a=Append[a,2];u=at[t,a];
    While[u=!=s,
      If[MatchQ[u,ap[ap[ap[s,s],_],_]],
        z=bit[u[[1,2]]];If[first===False,first=a];AppendTo[live,z];a=Append[a,2],
        assert[MatchQ[u,ap[ap[s,_],ap[_,_]]]&&first===False];last=bit[u[[2,1]]];
        spent=1-spent;a=Join[a,{1,2}]];u=at[t,a]]];
  assert[MatchQ[t,ap[ap[s,_],_]]];scanWord[{1,2}];rail={2};
  While[degree[at[t,rail]]===4,
    assert[MatchQ[at[t,Join[rail,{1,1}]],ap[ap[s,s],_]]];lp=Join[rail,{1,1,2}];
    assert[at[t,lp]=!=s];
    While[at[t,lp]=!=s,assert[degree[at[t,lp]]===2];sp=Join[lp,{1,2}];assert[degree[at[t,sp]]===2];
      za=Join[sp,{1,2}];oa=Append[sp,2];st={status[at[t,za]],status[at[t,oa]]};
      Which[st==={0,0},If[free===False,free={za,oa}],
        st==={1,0},assert[free===False];fired=1-fired,
        st==={0,1},assert[free===False];fired=1-fired;scanWord[Join[oa,{1,2}]],
        True,Throw[$Failed,bad]];lp=Append[lp,2]];
    rail=Append[rail,2]];
  assert[red[at[t,rail]]];stable=spent===fired;halt=stable&&first===False;
  selected=Which[stable&&first=!=False,first,stable||free===False,rail,
    True,assert[IntegerQ[last]];free[[last+1]]];assert[red[at[t,selected]]];
  {live,stable,selected,halt}],bad];
firstRed[t_,p_]:=Module[{q},Which[red[t],p,Head[t]=!=ap,False,
  True,q=firstRed[t[[1]],Append[p,1]];If[q===False,firstRed[t[[2]],Append[p,2]],q]]];
PureSStep[t_]:=Module[{v=PureSInspect[t],p},p=If[v===$Failed,firstRed[t,{}],v[[3]]];
  Which[p===False,t,p==={},act[t],True,ReplacePart[t,p->act[at[t,p]]]]];
PureSHalt[t_]:=Module[{v=PureSInspect[t]},If[v===$Failed,False,v[[4]]]];
PureSDecode[t_]:=Module[{v=PureSInspect[t]},If[v===$Failed,$Failed,v[[1]]]];
End[];
EndPackage[];
