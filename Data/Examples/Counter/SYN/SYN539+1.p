%--------------------------------------------------------------------------
% File     : SYN539+1 : TPTP v5.0.0. Released v2.1.0.
% Domain   : Syntactic (Translated)
% Problem  : ALC, N=5, R=1, L=40, K=3, D=2, P=0, Index=036
% Version  : Especial.
% English  :

% Refs     : [OS95]  Ohlbach & Schmidt (1995), Functional Translation and S
%          : [HS97]  Hustadt & Schmidt (1997), On Evaluating Decision Proce
%          : [Wei97] Weidenbach (1997), Email to G. Sutcliffe
% Source   : [Wei97]
% Names    : alc-5-1-40-3-2-036.dfg [Wei97]

% Status   : CounterSatisfiable
% Rating   : 0.00 v4.1.0, 0.17 v4.0.1, 0.00 v3.2.0, 0.25 v3.1.0, 0.17 v2.7.0, 0.50 v2.6.0, 0.25 v2.5.0, 0.00 v2.4.0, 0.00 v2.1.0
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :  370 (   0 equality)
%            Maximal formula depth :   43 (  43 average)
%            Number of connectives :  506 ( 137 ~  ; 148  |; 168  &)
%                                         (   0 <=>;  53 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   17 (   6 propositional; 0-2 arity)
%            Number of functors    :   53 (  53 constant; 0-0 arity)
%            Number of variables   :   53 (   0 singleton;  53 !;   0 ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_CSA_EPR

% Comments : These ALC problems have been translated from propositional
%            multi-modal K logic formulae generated according to the scheme
%            described in [HS97], using the optimized functional translation
%            described in [OS95]. The finite model property holds, the
%            Herbrand Universe is finite, they are decidable (the complexity
%            is PSPACE-complete), resolution + subsumption + condensing is a
%            decision procedure, and the translated formulae belong to the
%            (CNF-translation of the) Bernays-Schoenfinkel class [Wei97].
%--------------------------------------------------------------------------
fof(co1,conjecture,
    ( ~ ( ( c4_0
          | ( ndr1_0
            & c2_1(a587)
            & c3_1(a587)
            & c5_1(a587) ) )
        & ( ( ndr1_0
            & ndr1_1(a588)
            & ~ c1_2(a588,a589)
            & c2_2(a588,a589)
            & c3_2(a588,a589)
            & ndr1_1(a588)
            & ~ c4_2(a588,a590)
            & c2_2(a588,a590)
            & c1_2(a588,a590)
            & ndr1_1(a588)
            & c5_2(a588,a591)
            & ~ c2_2(a588,a591) )
          | ~ c2_0
          | ! [U] :
              ( ndr1_0
             => ( c2_1(U)
                | c5_1(U)
                | ~ c3_1(U) ) ) )
        & ( ~ c3_0
          | ~ c1_0
          | ~ c4_0 )
        & ( ( ndr1_0
            & ~ c3_1(a592)
            & ! [V] :
                ( ndr1_1(a592)
               => ( c5_2(a592,V)
                  | c4_2(a592,V)
                  | ~ c1_2(a592,V) ) )
            & ~ c4_1(a592) )
          | ( ndr1_0
            & ! [W] :
                ( ndr1_1(a593)
               => ( ~ c4_2(a593,W)
                  | c5_2(a593,W)
                  | ~ c1_2(a593,W) ) )
            & c2_1(a593)
            & ~ c5_1(a593) )
          | ( ndr1_0
            & c1_1(a594)
            & c4_1(a594) ) )
        & ( ~ c5_0
          | ! [X] :
              ( ndr1_0
             => ( ( ndr1_1(X)
                  & ~ c4_2(X,a595)
                  & ~ c1_2(X,a595) )
                | ~ c1_1(X)
                | ! [Y] :
                    ( ndr1_1(X)
                   => ( c2_2(X,Y)
                      | ~ c5_2(X,Y) ) ) ) ) )
        & ( ! [Z] :
              ( ndr1_0
             => ( c2_1(Z)
                | ! [X1] :
                    ( ndr1_1(Z)
                   => ( ~ c2_2(Z,X1)
                      | c3_2(Z,X1) ) )
                | c1_1(Z) ) )
          | c2_0
          | ( ndr1_0
            & ! [X2] :
                ( ndr1_1(a596)
               => ( c3_2(a596,X2)
                  | ~ c4_2(a596,X2)
                  | ~ c1_2(a596,X2) ) )
            & ndr1_1(a596)
            & c5_2(a596,a597)
            & ~ c2_2(a596,a597)
            & ~ c1_2(a596,a597)
            & ndr1_1(a596)
            & c1_2(a596,a598)
            & ~ c4_2(a596,a598)
            & c2_2(a596,a598) ) )
        & ( ! [X3] :
              ( ndr1_0
             => ( ( ndr1_1(X3)
                  & c2_2(X3,a599)
                  & ~ c3_2(X3,a599)
                  & ~ c5_2(X3,a599) )
                | ( ndr1_1(X3)
                  & c1_2(X3,a600)
                  & ~ c3_2(X3,a600)
                  & c2_2(X3,a600) )
                | c2_1(X3) ) )
          | ! [X4] :
              ( ndr1_0
             => ( ~ c3_1(X4)
                | c2_1(X4)
                | ( ndr1_1(X4)
                  & c4_2(X4,a601)
                  & c2_2(X4,a601)
                  & c5_2(X4,a601) ) ) )
          | c2_0 )
        & ( c1_0
          | ! [X5] :
              ( ndr1_0
             => ( ( ndr1_1(X5)
                  & ~ c2_2(X5,a602)
                  & c3_2(X5,a602) )
                | ( ndr1_1(X5)
                  & c5_2(X5,a603)
                  & c3_2(X5,a603)
                  & ~ c4_2(X5,a603) )
                | ( ndr1_1(X5)
                  & c4_2(X5,a604)
                  & c3_2(X5,a604)
                  & ~ c1_2(X5,a604) ) ) )
          | ! [X6] :
              ( ndr1_0
             => ( ! [X7] :
                    ( ndr1_1(X6)
                   => ( c4_2(X6,X7)
                      | c1_2(X6,X7)
                      | ~ c5_2(X6,X7) ) )
                | ~ c1_1(X6) ) ) )
        & ( ~ c1_0
          | ( ndr1_0
            & ! [X8] :
                ( ndr1_1(a605)
               => ( ~ c3_2(a605,X8)
                  | c2_2(a605,X8) ) )
            & ! [X9] :
                ( ndr1_1(a605)
               => ( c5_2(a605,X9)
                  | c3_2(a605,X9)
                  | ~ c1_2(a605,X9) ) ) )
          | ! [X10] :
              ( ndr1_0
             => ( ! [X11] :
                    ( ndr1_1(X10)
                   => ( c4_2(X10,X11)
                      | c5_2(X10,X11) ) )
                | c3_1(X10) ) ) )
        & ( ! [X12] :
              ( ndr1_0
             => ( ( ndr1_1(X12)
                  & c4_2(X12,a606)
                  & c3_2(X12,a606) )
                | ~ c3_1(X12)
                | ! [X13] :
                    ( ndr1_1(X12)
                   => ( ~ c2_2(X12,X13)
                      | c3_2(X12,X13)
                      | c5_2(X12,X13) ) ) ) )
          | c5_0 )
        & ( ! [X14] :
              ( ndr1_0
             => ( c4_1(X14)
                | ( ndr1_1(X14)
                  & ~ c1_2(X14,a607)
                  & c4_2(X14,a607)
                  & c3_2(X14,a607) )
                | c2_1(X14) ) )
          | ~ c2_0
          | c5_0 )
        & ( ! [X15] :
              ( ndr1_0
             => ( ~ c1_1(X15)
                | ! [X16] :
                    ( ndr1_1(X15)
                   => ( c5_2(X15,X16)
                      | c4_2(X15,X16) ) )
                | ~ c3_1(X15) ) )
          | ( ndr1_0
            & ! [X17] :
                ( ndr1_1(a608)
               => ( ~ c3_2(a608,X17)
                  | c2_2(a608,X17) ) )
            & ! [X18] :
                ( ndr1_1(a608)
               => ( ~ c2_2(a608,X18)
                  | ~ c5_2(a608,X18) ) )
            & ndr1_1(a608)
            & c5_2(a608,a609)
            & ~ c4_2(a608,a609) )
          | ! [X19] :
              ( ndr1_0
             => ( c5_1(X19)
                | ( ndr1_1(X19)
                  & c2_2(X19,a610)
                  & c3_2(X19,a610)
                  & ~ c1_2(X19,a610) )
                | c1_1(X19) ) ) )
        & ( ~ c4_0
          | ~ c2_0
          | ( ndr1_0
            & ndr1_1(a611)
            & c5_2(a611,a612)
            & ~ c1_2(a611,a612)
            & ! [X20] :
                ( ndr1_1(a611)
               => ( c5_2(a611,X20)
                  | ~ c3_2(a611,X20)
                  | c2_2(a611,X20) ) )
            & ~ c1_1(a611) ) )
        & ( ~ c3_0
          | ! [X21] :
              ( ndr1_0
             => ( ~ c3_1(X21)
                | c5_1(X21) ) )
          | ( ndr1_0
            & ~ c3_1(a613)
            & ndr1_1(a613)
            & c1_2(a613,a614)
            & ~ c4_2(a613,a614)
            & ~ c3_2(a613,a614)
            & ! [X22] :
                ( ndr1_1(a613)
               => ( ~ c2_2(a613,X22)
                  | c1_2(a613,X22) ) ) ) )
        & ( ( ndr1_0
            & ~ c1_1(a615)
            & ! [X23] :
                ( ndr1_1(a615)
               => ( ~ c5_2(a615,X23)
                  | ~ c2_2(a615,X23)
                  | ~ c3_2(a615,X23) ) )
            & ! [X24] :
                ( ndr1_1(a615)
               => ( ~ c2_2(a615,X24)
                  | c3_2(a615,X24)
                  | c1_2(a615,X24) ) ) )
          | ~ c1_0
          | ~ c3_0 )
        & ( c4_0
          | ~ c5_0
          | ( ndr1_0
            & ~ c3_1(a616)
            & c1_1(a616)
            & ~ c2_1(a616) ) )
        & ( ~ c2_0
          | ! [X25] :
              ( ndr1_0
             => ( ( ndr1_1(X25)
                  & c4_2(X25,a617)
                  & ~ c1_2(X25,a617) )
                | c1_1(X25)
                | ! [X26] :
                    ( ndr1_1(X25)
                   => ( ~ c5_2(X25,X26)
                      | c2_2(X25,X26)
                      | ~ c1_2(X25,X26) ) ) ) ) )
        & ( ! [X27] :
              ( ndr1_0
             => ( c1_1(X27)
                | ( ndr1_1(X27)
                  & ~ c4_2(X27,a618)
                  & ~ c3_2(X27,a618)
                  & ~ c2_2(X27,a618) )
                | ~ c2_1(X27) ) )
          | c2_0
          | c4_0 )
        & ( ~ c5_0
          | ( ndr1_0
            & c4_1(a619)
            & c1_1(a619)
            & c5_1(a619) )
          | c1_0 )
        & ( c4_0
          | ~ c3_0
          | c1_0 )
        & ( ~ c5_0
          | ~ c1_0
          | ( ndr1_0
            & ~ c4_1(a620) ) )
        & ( ! [X28] :
              ( ndr1_0
             => c2_1(X28) )
          | c2_0
          | ! [X29] :
              ( ndr1_0
             => ( ~ c2_1(X29)
                | ( ndr1_1(X29)
                  & c1_2(X29,a621)
                  & c4_2(X29,a621)
                  & ~ c2_2(X29,a621) )
                | ( ndr1_1(X29)
                  & ~ c1_2(X29,a622)
                  & c5_2(X29,a622) ) ) ) )
        & ( ~ c4_0
          | ! [X30] :
              ( ndr1_0
             => ( ~ c2_1(X30)
                | ! [X31] :
                    ( ndr1_1(X30)
                   => ( c2_2(X30,X31)
                      | ~ c1_2(X30,X31)
                      | ~ c4_2(X30,X31) ) )
                | c4_1(X30) ) )
          | ~ c3_0 )
        & ( ~ c4_0
          | ~ c1_0
          | ! [X32] :
              ( ndr1_0
             => ( ( ndr1_1(X32)
                  & ~ c3_2(X32,a623) )
                | ~ c3_1(X32)
                | ! [X33] :
                    ( ndr1_1(X32)
                   => ( ~ c4_2(X32,X33)
                      | c1_2(X32,X33)
                      | ~ c2_2(X32,X33) ) ) ) ) )
        & ( ( ndr1_0
            & ! [X34] :
                ( ndr1_1(a624)
               => ( c3_2(a624,X34)
                  | c2_2(a624,X34)
                  | c5_2(a624,X34) ) )
            & ndr1_1(a624)
            & c3_2(a624,a625)
            & ~ c1_2(a624,a625)
            & ~ c2_2(a624,a625)
            & ndr1_1(a624)
            & c5_2(a624,a626)
            & ~ c3_2(a624,a626)
            & c4_2(a624,a626) )
          | c2_0
          | ! [X35] :
              ( ndr1_0
             => ( ~ c3_1(X35)
                | ( ndr1_1(X35)
                  & ~ c2_2(X35,a627)
                  & c1_2(X35,a627) )
                | ! [X36] :
                    ( ndr1_1(X35)
                   => ( ~ c5_2(X35,X36)
                      | ~ c1_2(X35,X36)
                      | ~ c3_2(X35,X36) ) ) ) ) )
        & ( ! [X37] :
              ( ndr1_0
             => ( ! [X38] :
                    ( ndr1_1(X37)
                   => ( c2_2(X37,X38)
                      | ~ c1_2(X37,X38)
                      | c3_2(X37,X38) ) )
                | ( ndr1_1(X37)
                  & c4_2(X37,a628)
                  & ~ c1_2(X37,a628)
                  & ~ c5_2(X37,a628) )
                | ~ c4_1(X37) ) )
          | ( ndr1_0
            & ndr1_1(a629)
            & ~ c2_2(a629,a630)
            & ~ c5_2(a629,a630)
            & ~ c2_1(a629)
            & c3_1(a629) )
          | ~ c3_0 )
        & ( ~ c4_0
          | ( ndr1_0
            & c1_1(a631)
            & ~ c3_1(a631) ) )
        & ( ! [X39] :
              ( ndr1_0
             => ( ! [X40] :
                    ( ndr1_1(X39)
                   => ( c3_2(X39,X40)
                      | ~ c1_2(X39,X40)
                      | c5_2(X39,X40) ) )
                | c2_1(X39)
                | ( ndr1_1(X39)
                  & ~ c2_2(X39,a632)
                  & ~ c3_2(X39,a632) ) ) )
          | c3_0
          | ( ndr1_0
            & ~ c3_1(a633)
            & ! [X41] :
                ( ndr1_1(a633)
               => ( c1_2(a633,X41)
                  | ~ c3_2(a633,X41) ) )
            & ~ c1_1(a633) ) )
        & ( ( ndr1_0
            & ~ c2_1(a634) )
          | ! [X42] :
              ( ndr1_0
             => ( ( ndr1_1(X42)
                  & ~ c2_2(X42,a635) )
                | ~ c5_1(X42)
                | ! [X43] :
                    ( ndr1_1(X42)
                   => ( c2_2(X42,X43)
                      | ~ c1_2(X42,X43) ) ) ) )
          | c1_0 )
        & ( c3_0
          | ~ c1_0
          | c5_0 )
        & ( ~ c5_0
          | ~ c2_0
          | ! [X44] :
              ( ndr1_0
             => ( ! [X45] :
                    ( ndr1_1(X44)
                   => ( c1_2(X44,X45)
                      | ~ c2_2(X44,X45) ) )
                | ! [X46] :
                    ( ndr1_1(X44)
                   => ( c4_2(X44,X46)
                      | ~ c2_2(X44,X46) ) )
                | ( ndr1_1(X44)
                  & c2_2(X44,a636)
                  & ~ c3_2(X44,a636) ) ) ) )
        & c5_0
        & ( c3_0
          | ( ndr1_0
            & ~ c3_1(a637)
            & ~ c2_1(a637)
            & ndr1_1(a637)
            & c1_2(a637,a638)
            & ~ c4_2(a637,a638) ) )
        & ( ! [X47] :
              ( ndr1_0
             => ( ( ndr1_1(X47)
                  & ~ c1_2(X47,a639)
                  & ~ c2_2(X47,a639)
                  & c5_2(X47,a639) )
                | ~ c5_1(X47)
                | c3_1(X47) ) )
          | c4_0 ) ) )).

%--------------------------------------------------------------------------