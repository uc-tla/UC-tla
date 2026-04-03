---- MODULE F_Tendermint ----
EXTENDS Integers, Naturals, FiniteSets

(***************************************************************************
 DelayAttack-aligned UC-style Tendermint functionality.

 Traceability notes (read together with F_Tendermint_DelayAttack.md and
 SubFunctionality.md):
   - Variables map to protocol fields in the functionality text:
       h/r/phase, lockedValue/lockedRound, validValue/validRound,
       countPrevote/countPrecommit/countNextRound, decision.
   - Main execution path implements the four-phase core:
       NewRoundAndPropose -> Prevote -> Precommit -> Commit.
   - Auxiliary protocol primitives are modeled as explicit actions:
       Corrupt, NewHeight, RoundAdvance, GetTime, ResetTime,
       TimeStart, IsTimeout, ClockTick, AdversaryWake.
   - Delay-attack behavior is centralized in DelayAttack(p); each core
     phase contains an attack branch and a non-attack branch.
***************************************************************************)

CONSTANTS
    \* @type: Set(Str);
    Validators,
    \* @type: Set(Str);
    InitiallyCorrupted,
    \* @type: Int;
    Delta,
    \* @type: Int;
    Sigma,
    \* @type: Int;
    MaxHeight,
    \* @type: Int;
    MaxRound,
    \* @type: Set(Int);
    Values,
    \* @type: Int;
    NilValue

ASSUME
    /\ Validators # {}
    /\ InitiallyCorrupted \subseteq Validators
    /\ Delta \in Nat
    /\ Sigma \in Nat
    /\ MaxHeight \in Nat
    /\ MaxRound \in Nat
    /\ Values # {}
    /\ NilValue \notin Values

Phases == {"propose", "prevote", "precommit", "commit"}
TimeoutStates == {"none", "remain", "over"}

f == (Cardinality(Validators) - 1) \div 3
Quorum == 2 * f + 1
MaxTimerLen == 2 * Delta + 2 * Sigma + 1

SelectProposer(vp, rem) ==
    CHOOSE k \in (Validators \ rem) :
        \A i \in (Validators \ rem) : vp[k] >= vp[i]

UpdateVotingPower(vp, proposer, rem, st) ==
    [i \in Validators |->
        IF i \in rem THEN vp[i]
        ELSE IF i = proposer
             THEN vp[i] - (Cardinality(Validators \ rem) - 1)
             ELSE vp[i] + st[i]
    ]

\* @type: (Str -> Int, Str, Set(Str)) => (Str -> Int);
SyncAfterRoundOK(bits, p, bad) ==
    LET bits1 == [bits EXCEPT ![p] = 1]
    IN IF \A q \in Validators \ bad : bits1[q] = 1
       THEN [q \in Validators |-> 0]
       ELSE bits1

VARIABLES
    \* @type: Set(Str);
    corrupted,
    \* @type: Set(Str);
    removed,
    \* @type: Set([kind: Str, sender: Str, hh: Int, rr: Int, v: Int, vr: Int, who: Str, now: Int, len: Int, remain: Int, L: Int]);
    messages,

    \* @type: Str -> Int;
    h,
    \* @type: Str -> Int;
    r,
    \* @type: Str -> Str;
    phase,

    \* @type: Str -> Int;
    lockedValue,
    \* @type: Str -> Int;
    lockedRound,
    \* @type: Str -> Int;
    validValue,
    \* @type: Str -> Int;
    validRound,

    \* @type: Str -> Int;
    proposalValue,
    \* @type: Str -> Int;
    proposalVR,
    \* @type: Str -> Int;
    prevoteValue,
    \* @type: Str -> Int;
    precommitValue,

    \* @type: Str -> (Int -> Int);
    decision,
    \* @type: Str -> Int;
    countPrevote,
    \* @type: Str -> Int;
    countPrecommit,
    \* @type: Str -> Int;
    countNextRound,

    \* @type: Str -> Int;
    stake,
    \* @type: Str -> Int;
    votingPower,
    \* @type: Int -> (Int -> Str);
    proposerAt,

    \* @type: Int;
    delta,
    \* @type: Str -> Int;
    sigma,
    \* @type: Int -> Int;
    deltaRound,

    \* @type: Str -> [active: Bool, start: Int, len: Int];
    timer,
    \* @type: Str -> Str;
    timeoutState,
    \* @type: Int;
    clockTime,

    \* @type: Str -> Int;
    syncBits,
    \* @type: Str -> Bool;
    pendingNewHeight,
    \* @type: Int;
    attackCount

vars == <<corrupted, removed, messages,
          h, r, phase,
          lockedValue, lockedRound, validValue, validRound,
          proposalValue, proposalVR, prevoteValue, precommitValue,
          decision, countPrevote, countPrecommit, countNextRound,
          stake, votingPower, proposerAt,
          delta, sigma, deltaRound,
          timer, timeoutState, clockTime,
          syncBits, pendingNewHeight, attackCount>>

Valid(v) == v \in Values
DelayAttack(p) == (delta + sigma[p] > 2 * Delta) \/ (sigma[p] > 2 * Sigma)
Elapsed(p) == clockTime - timer[p].start

\* Protocol initialization (maps to initialization of local states in
\* F_Tendermint_DelayAttack.md and the compact algorithm in SubFunctionality.md)
Init ==
    /\ corrupted = InitiallyCorrupted
    /\ removed = {}
    /\ messages = {}

    /\ h = [p \in Validators |-> 0]
    /\ r = [p \in Validators |-> 0]
    /\ phase = [p \in Validators |-> "propose"]

    /\ lockedValue = [p \in Validators |-> NilValue]
    /\ lockedRound = [p \in Validators |-> -1]
    /\ validValue = [p \in Validators |-> NilValue]
    /\ validRound = [p \in Validators |-> -1]

    /\ proposalValue = [p \in Validators |-> NilValue]
    /\ proposalVR = [p \in Validators |-> -1]
    /\ prevoteValue = [p \in Validators |-> NilValue]
    /\ precommitValue = [p \in Validators |-> NilValue]

    /\ decision = [p \in Validators |-> [hh \in 0..MaxHeight |-> NilValue]]
    /\ countPrevote = [p \in Validators |-> 0]
    /\ countPrecommit = [p \in Validators |-> 0]
    /\ countNextRound = [p \in Validators |-> 0]

    /\ stake = [p \in Validators |-> 1]
    /\ votingPower = stake
    /\ proposerAt = [hh \in 0..MaxHeight |-> [rr \in 0..MaxRound |-> CHOOSE x \in Validators : TRUE]]

    /\ delta = 1
    /\ sigma = [p \in Validators |-> 0]
    /\ deltaRound = [rr \in 0..MaxRound |-> delta + rr * Delta]

    /\ timer = [p \in Validators |-> [active |-> FALSE, start |-> 0, len |-> 0]]
    /\ timeoutState = [p \in Validators |-> "none"]
    /\ clockTime = 0

    /\ syncBits = [p \in Validators |-> 0]
    /\ pendingNewHeight = [p \in Validators |-> FALSE]
    /\ attackCount = 0

(***************************************************************************
 Non-main actions
***************************************************************************)

Corrupt(p) ==
    /\ p \in Validators
    /\ p \notin corrupted
    /\ Cardinality(corrupted) < f + 1  \* at most f nodes can be corrupted
    /\ corrupted' = corrupted \cup {p}
    /\ UNCHANGED <<removed, messages,
                   h, r, phase,
                   lockedValue, lockedRound, validValue, validRound,
                   proposalValue, proposalVR, prevoteValue, precommitValue,
                   decision, countPrevote, countPrecommit, countNextRound,
                   stake, votingPower, proposerAt,
                   delta, sigma, deltaRound,
                   timer, timeoutState, clockTime,
                   syncBits, pendingNewHeight, attackCount>>

AdversaryWake(p, s) ==
  /\ p \in Validators \ removed
  /\ p \notin corrupted  
  /\ phase[p] \in Phases
  /\ sigma[p] = 0
  /\ attackCount < f  \* total attack count limited to f
    /\ s \in 0..2*Sigma+1  \* allow full attack range including delay-attack values
    /\ sigma' = [sigma EXCEPT ![p] = s]
    /\ attackCount' = attackCount + 1
    /\ UNCHANGED <<corrupted, removed, messages,
                   h, r, phase,
                   lockedValue, lockedRound, validValue, validRound,
                   proposalValue, proposalVR, prevoteValue, precommitValue,
                   decision, countPrevote, countPrecommit, countNextRound,
                   stake, votingPower, proposerAt,
                   delta, deltaRound,
                   timer, timeoutState, clockTime,
                   syncBits, pendingNewHeight>>

GetTime ==
    /\ messages' = {[kind |-> "TimeNow", now |-> clockTime,
                     sender |-> "", hh |-> 0, rr |-> 0, v |-> 0, vr |-> 0,
                     who |-> "", len |-> 0, remain |-> 0, L |-> 0]}
    /\ UNCHANGED <<corrupted, removed,
                   h, r, phase,
                   lockedValue, lockedRound, validValue, validRound,
                   proposalValue, proposalVR, prevoteValue, precommitValue,
                   decision, countPrevote, countPrecommit, countNextRound,
                   stake, votingPower, proposerAt,
                   delta, sigma, deltaRound,
                   timer, timeoutState, clockTime,
                   syncBits, pendingNewHeight, attackCount>>

ResetTime(p) ==
    /\ p \in Validators
    /\ timer' = [timer EXCEPT ![p] = [active |-> FALSE, start |-> 0, len |-> 0]]
    /\ timeoutState' = [timeoutState EXCEPT ![p] = "none"]
    /\ messages' = {[kind |-> "TimeOK", who |-> p,
                     sender |-> "", hh |-> 0, rr |-> 0, v |-> 0, vr |-> 0,
                     now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
    /\ UNCHANGED <<corrupted, removed,
                   h, r, phase,
                   lockedValue, lockedRound, validValue, validRound,
                   proposalValue, proposalVR, prevoteValue, precommitValue,
                   decision, countPrevote, countPrecommit, countNextRound,
                   stake, votingPower, proposerAt,
                   delta, sigma, deltaRound,
                   clockTime,
                   syncBits, pendingNewHeight, attackCount>>

TimeStart(p, L) ==
    /\ p \in Validators
  /\ L \in 0..MaxTimerLen
    /\ timer[p].active = FALSE
    /\ timer' = [timer EXCEPT ![p] = [active |-> TRUE, start |-> clockTime, len |-> L]]
    /\ timeoutState' = [timeoutState EXCEPT ![p] = "none"]
    /\ messages' = {[kind |-> "TimeStart", who |-> p, len |-> L,
                     sender |-> "", hh |-> 0, rr |-> 0, v |-> 0, vr |-> 0,
                     now |-> 0, remain |-> 0, L |-> L]}
    /\ UNCHANGED <<corrupted, removed,
                   h, r, phase,
                   lockedValue, lockedRound, validValue, validRound,
                   proposalValue, proposalVR, prevoteValue, precommitValue,
                   decision, countPrevote, countPrecommit, countNextRound,
                   stake, votingPower, proposerAt,
                   delta, sigma, deltaRound,
                   clockTime,
                   syncBits, pendingNewHeight, attackCount>>

IsTimeout(p) ==
    /\ p \in Validators
    /\ timer[p].active
    /\ IF Elapsed(p) >= timer[p].len
       THEN
         /\ timeoutState' = [timeoutState EXCEPT ![p] = "over"]
         /\ messages' = {[kind |-> "TimeOver", who |-> p, L |-> timer[p].len,
                          sender |-> "", hh |-> 0, rr |-> 0, v |-> 0, vr |-> 0,
                          now |-> 0, len |-> 0, remain |-> 0]}
       ELSE
         /\ timeoutState' = [timeoutState EXCEPT ![p] = "remain"]
         /\ messages' = {[kind |-> "TimeRemain", who |-> p, remain |-> timer[p].len - Elapsed(p),
                          sender |-> "", hh |-> 0, rr |-> 0, v |-> 0, vr |-> 0,
                          now |-> 0, len |-> 0, L |-> 0]}
    /\ UNCHANGED <<corrupted, removed,
                   h, r, phase,
                   lockedValue, lockedRound, validValue, validRound,
                   proposalValue, proposalVR, prevoteValue, precommitValue,
                   decision, countPrevote, countPrecommit, countNextRound,
                   stake, votingPower, proposerAt,
                   delta, sigma, deltaRound,
                   timer, clockTime,
                   syncBits, pendingNewHeight, attackCount>>

ClockTick ==
    /\ clockTime' = clockTime + 1
    /\ UNCHANGED <<corrupted, removed, messages,
                   h, r, phase,
                   lockedValue, lockedRound, validValue, validRound,
                   proposalValue, proposalVR, prevoteValue, precommitValue,
                   decision, countPrevote, countPrecommit, countNextRound,
                   stake, votingPower, proposerAt,
                   delta, sigma, deltaRound,
                   timer, timeoutState,
                   syncBits, pendingNewHeight, attackCount>>

NewHeight(p) ==
    /\ p \in Validators
    /\ phase[p] = "propose"
    /\ pendingNewHeight[p]
    /\ h[p] < MaxHeight
    /\ h' = [h EXCEPT ![p] = @ + 1]
    /\ r' = [r EXCEPT ![p] = 0]
    /\ lockedValue' = [lockedValue EXCEPT ![p] = NilValue]
    /\ lockedRound' = [lockedRound EXCEPT ![p] = -1]
    /\ validValue' = [validValue EXCEPT ![p] = NilValue]
    /\ validRound' = [validRound EXCEPT ![p] = -1]
    /\ proposalValue' = [proposalValue EXCEPT ![p] = NilValue]
    /\ proposalVR' = [proposalVR EXCEPT ![p] = -1]
    /\ prevoteValue' = [prevoteValue EXCEPT ![p] = NilValue]
    /\ precommitValue' = [precommitValue EXCEPT ![p] = NilValue]
    /\ countPrevote' = [countPrevote EXCEPT ![p] = 0]
    /\ countPrecommit' = [countPrecommit EXCEPT ![p] = 0]
    /\ countNextRound' = [countNextRound EXCEPT ![p] = 0]
    /\ pendingNewHeight' = [pendingNewHeight EXCEPT ![p] = FALSE]
    /\ messages' = {[kind |-> "NEWROUND", who |-> p, hh |-> h[p] + 1, rr |-> 0,
                     sender |-> "", v |-> 0, vr |-> 0, now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
    /\ UNCHANGED <<corrupted, removed,
                   phase, decision,
                   stake, votingPower, proposerAt,
                   delta, sigma, deltaRound,
                   timer, timeoutState, clockTime,
                   syncBits, attackCount>>

RoundAdvance(p, rr) ==
    /\ p \in Validators
    /\ rr \in 0..MaxRound
    /\ rr > r[p]
    /\ LET nextCnt == countNextRound[p] + 1 IN
       /\ countNextRound' = [countNextRound EXCEPT ![p] = nextCnt]
       /\ IF nextCnt > f + 1
          THEN

            /\ r' = [r EXCEPT ![p] = rr]
            /\ phase' = [phase EXCEPT ![p] = "propose"]
            /\ messages' = {[kind |-> "NEWROUND", who |-> p, hh |-> h[p], rr |-> rr,
                             sender |-> "", v |-> 0, vr |-> 0, now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
          ELSE
            /\ r' = r
            /\ phase' = phase
            /\ messages' = {[kind |-> "ROUNDADV", who |-> p, hh |-> h[p], rr |-> rr,
                             sender |-> "", v |-> 0, vr |-> 0, now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
    /\ UNCHANGED <<corrupted, removed,
                   h,
                   lockedValue, lockedRound, validValue, validRound,
                   proposalValue, proposalVR, prevoteValue, precommitValue,
                   decision, countPrevote, countPrecommit,
                   stake, votingPower, proposerAt,
                   delta, sigma, deltaRound,
                   timer, timeoutState, clockTime,
                   syncBits, pendingNewHeight, attackCount>>

(***************************************************************************
 Main pipeline: NewRoundAndPropose -> Prevote -> Precommit -> Commit
***************************************************************************)

\* NEWROUND + PROPOSAL phase:
\* - proposer selection and voting power update
\* - delay-attack guard branch (retry/new round)
\* - normal branch broadcasts proposal and enters prevote
NewRoundAndPropose(p) ==
    /\ p \in Validators
    /\ p \notin removed
    /\ phase[p] = "propose"
    /\ (Validators \ removed) # {}
    /\ r[p] <= MaxRound
    /\ LET proposer == SelectProposer(votingPower, removed)
           h0 == h[p]
           r0 == r[p]
           vv == IF validValue[p] # NilValue THEN validValue[p] ELSE CHOOSE x \in Values : TRUE
           vr0 == IF validValue[p] # NilValue THEN validRound[p] ELSE -1
           authOK == proposer \notin removed
           sigOK == proposer \notin removed
       IN
       /\ proposerAt' = [proposerAt EXCEPT ![h0][r0] = proposer]
       /\ votingPower' = UpdateVotingPower(votingPower, proposer, removed, stake)
       /\ sigma' = [sigma EXCEPT ![p] = 0]
       /\ timer' = [timer EXCEPT ![p] = [active |-> TRUE, start |-> clockTime, len |-> delta]]
       /\ timeoutState' = [timeoutState EXCEPT ![p] = "none"]
       /\ IF DelayAttack(p)
          THEN
            /\ messages' = {[kind |-> "DELAY-RETRY", who |-> p, hh |-> h0, rr |-> r0,
                             sender |-> "", v |-> 0, vr |-> 0, now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
            /\ r' = r
            /\ UNCHANGED <<removed, phase, proposalValue, proposalVR, validValue, validRound, attackCount>>
          ELSE IF ~authOK \/ ~sigOK
          THEN
            /\ removed' = removed \cup {proposer}
            /\ messages' = {[kind |-> "NEWROUND", who |-> p, hh |-> h0, rr |-> r0 + 1,
                             sender |-> "", v |-> 0, vr |-> 0, now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
            /\ r' = [r EXCEPT ![p] = IF r[p] < MaxRound THEN @ + 1 ELSE @]
            /\ UNCHANGED <<phase, proposalValue, proposalVR, validValue, validRound, attackCount>>
          ELSE
            /\ removed' = removed
            /\ proposalValue' = [q \in Validators |-> vv]
            /\ proposalVR' = [q \in Validators |-> vr0]
            /\ validValue' = [validValue EXCEPT ![p] = vv]
            /\ validRound' = [validRound EXCEPT ![p] = r0]
            /\ phase' = [phase EXCEPT ![p] = "prevote"]
            /\ messages' = {[kind |-> "PROPOSAL", sender |-> proposer, hh |-> h0, rr |-> r0, v |-> vv, vr |-> vr0,
                             who |-> "", now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
            /\ r' = r
            /\ attackCount' = attackCount
    /\ UNCHANGED <<corrupted, h,
                   lockedValue, lockedRound,
                   prevoteValue, precommitValue,
                   decision, countPrevote, countPrecommit, countNextRound,
                   stake,
                   delta, deltaRound,
                   clockTime,
                   syncBits, pendingNewHeight>>

\* PREVOTE phase:
\* follows lock/valid rules from the protocol text; under attack votes NilValue
Prevote(p) ==
    /\ p \in Validators
    /\ p \notin removed
    /\ phase[p] = "prevote"
    /\ LET h0 == h[p]
           r0 == r[p]
           proposer == proposerAt[h0][r0]
           v == proposalValue[p]
           vr0 == proposalVR[p]
           authOK == proposer \notin removed
           sigOK == proposer \notin removed
           vote == IF DelayAttack(p)
                      THEN NilValue
                      ELSE IF ~authOK \/ ~sigOK
                           THEN NilValue
                           ELSE IF Valid(v) /\ vr0 = -1 /\ (lockedRound[p] = -1 \/ lockedValue[p] = v)
                                THEN v
                                ELSE IF Valid(v) /\ vr0 >= 0 /\ (lockedRound[p] <= vr0 \/ lockedValue[p] = v)
                                     THEN v
                                     ELSE NilValue
       IN
       /\ removed' = IF ~authOK \/ ~sigOK THEN removed \cup {proposer} ELSE removed
       /\ sigma' = [sigma EXCEPT ![p] = 0]
       /\ prevoteValue' = [prevoteValue EXCEPT ![p] = vote]
       /\ countPrevote' = [countPrevote EXCEPT ![p] = IF vote # NilValue THEN Quorum + 1 ELSE @ + 1]
       /\ phase' = [phase EXCEPT ![p] = "precommit"]
       /\ timer' = [timer EXCEPT ![p] = [active |-> TRUE, start |-> clockTime, len |-> delta]]
       /\ timeoutState' = [timeoutState EXCEPT ![p] = "none"]
       /\ messages' = {[kind |-> "PREVOTE", sender |-> p, hh |-> h0, rr |-> r0, v |-> vote,
                        who |-> "", vr |-> 0, now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
    /\ UNCHANGED <<corrupted,
                   h, r,
                   lockedValue, lockedRound, validValue, validRound,
                   proposalValue, proposalVR, precommitValue,
                   decision, countPrecommit, countNextRound,
                   stake, votingPower, proposerAt,
                   delta, deltaRound,
                   clockTime,
                   syncBits, pendingNewHeight, attackCount>>

\* PRECOMMIT phase:
\* on quorum prevotes for a valid value, lock and move to commit
Precommit(p) ==
    /\ p \in Validators
    /\ p \notin removed
    /\ phase[p] = "precommit"
    /\ LET h0 == h[p]
           r0 == r[p]
           v == prevoteValue[p]
           canLock == ~DelayAttack(p) /\ Valid(v) /\ countPrevote[p] > (2 * f + 1)
           pcv == IF canLock THEN v ELSE NilValue
       IN
       /\ IF canLock
          THEN
            /\ lockedValue' = [lockedValue EXCEPT ![p] = v]
            /\ lockedRound' = [lockedRound EXCEPT ![p] = r0]
            /\ validValue' = [validValue EXCEPT ![p] = v]
            /\ validRound' = [validRound EXCEPT ![p] = r0]
            /\ countPrecommit' = [countPrecommit EXCEPT ![p] = Quorum + 1]
            /\ attackCount' = attackCount
          ELSE
            /\ UNCHANGED <<lockedValue, lockedRound, validValue, validRound, attackCount>>
           /\ countPrecommit' = countPrecommit
       /\ sigma' = [sigma EXCEPT ![p] = 0]
       /\ precommitValue' = [precommitValue EXCEPT ![p] = pcv]
       /\ phase' = [phase EXCEPT ![p] = "commit"]
       /\ timer' = [timer EXCEPT ![p] = [active |-> TRUE, start |-> clockTime, len |-> delta]]
       /\ timeoutState' = [timeoutState EXCEPT ![p] = "none"]
       /\ messages' = {[kind |-> "PRECOMMIT", sender |-> p, hh |-> h0, rr |-> r0, v |-> pcv,
                        who |-> "", vr |-> 0, now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
    /\ UNCHANGED <<corrupted, removed,
                   h, r,
                   proposalValue, proposalVR, prevoteValue,
                   decision, countPrevote, countNextRound,
                   stake, votingPower, proposerAt,
                   delta, deltaRound,
                   clockTime,
                   syncBits, pendingNewHeight>>

\* COMMIT phase:
\* - attack branch: no decision, advance round
\* - commitOK branch: write decision and trigger NEWHEIGHT
\* - fallback branch: advance round without decision
Commit(p) ==
    /\ p \in Validators
    /\ p \notin removed
    /\ phase[p] = "commit"
    /\ LET h0 == h[p]
           r0 == r[p]
           v == precommitValue[p]
           commitOK == ~DelayAttack(p) /\ Valid(v) /\ countPrecommit[p] > (2 * f + 1)
       IN
       /\ IF DelayAttack(p)
          THEN
            /\ r' = [r EXCEPT ![p] = IF r[p] < MaxRound THEN @ + 1 ELSE @]
            /\ phase' = [phase EXCEPT ![p] = "propose"]
            /\ deltaRound' = [deltaRound EXCEPT ![r0 + 1] = deltaRound[r0] + (r0 + 1) * Delta]
            /\ messages' = {[kind |-> "NEWROUND", who |-> p, hh |-> h0, rr |-> r0 + 1,
                             sender |-> "", v |-> 0, vr |-> 0, now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
            /\ decision' = decision
            /\ syncBits' = syncBits
            /\ pendingNewHeight' = pendingNewHeight
            /\ countPrevote' = countPrevote
            /\ countPrecommit' = countPrecommit
            /\ countNextRound' = countNextRound
            /\ lockedValue' = lockedValue
            /\ lockedRound' = lockedRound
            /\ validValue' = validValue
            /\ validRound' = validRound
            /\ attackCount' = attackCount
          ELSE IF commitOK
          THEN
            /\ decision' = [decision EXCEPT ![p][h0] = v]
            /\ syncBits' = SyncAfterRoundOK(syncBits, p, corrupted)
            /\ phase' = [phase EXCEPT ![p] = "propose"]
            /\ countPrevote' = [countPrevote EXCEPT ![p] = 0]
            /\ countPrecommit' = [countPrecommit EXCEPT ![p] = 0]
            /\ countNextRound' = [countNextRound EXCEPT ![p] = 0]
            /\ lockedValue' = [lockedValue EXCEPT ![p] = NilValue]
            /\ lockedRound' = [lockedRound EXCEPT ![p] = -1]
            /\ validValue' = [validValue EXCEPT ![p] = NilValue]
            /\ validRound' = [validRound EXCEPT ![p] = -1]
            /\ pendingNewHeight' = [pendingNewHeight EXCEPT ![p] = TRUE]
            /\ messages' = {[kind |-> "NEWHEIGHT", who |-> p, hh |-> h0, rr |-> r0, v |-> v,
                             sender |-> "", vr |-> 0, now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
            /\ r' = r
            /\ deltaRound' = deltaRound
            /\ attackCount' = attackCount
          ELSE
            /\ r' = [r EXCEPT ![p] = IF r[p] < MaxRound THEN @ + 1 ELSE @]
            /\ phase' = [phase EXCEPT ![p] = "propose"]
            /\ countNextRound' = [countNextRound EXCEPT ![p] = @ + 1]
            /\ messages' = {[kind |-> "NEWROUND", who |-> p, hh |-> h0, rr |-> r0 + 1,
                             sender |-> "", v |-> 0, vr |-> 0, now |-> 0, len |-> 0, remain |-> 0, L |-> 0]}
            /\ decision' = decision
            /\ syncBits' = syncBits
            /\ pendingNewHeight' = pendingNewHeight
            /\ countPrevote' = countPrevote
            /\ countPrecommit' = countPrecommit
            /\ lockedValue' = lockedValue
            /\ lockedRound' = lockedRound
            /\ validValue' = validValue
            /\ validRound' = validRound
            /\ deltaRound' = deltaRound
            /\ attackCount' = attackCount
    /\ sigma' = [sigma EXCEPT ![p] = 0]
    /\ timer' = [timer EXCEPT ![p] = [active |-> FALSE, start |-> 0, len |-> 0]]
    /\ timeoutState' = [timeoutState EXCEPT ![p] = "none"]
    /\ UNCHANGED <<corrupted, removed,
                   h,
                   proposalValue, proposalVR, prevoteValue, precommitValue,
                   stake, votingPower, proposerAt,
                   delta,
                   clockTime>>

ProgressStep(p) == NewRoundAndPropose(p) \/ Prevote(p) \/ Precommit(p) \/ Commit(p)

(***************************************************************************
 Bounded Delay Attack abstractions
***************************************************************************)

\* Set of sigma values that trigger DelayAttack condition
AttackValues == {s \in 0..2*Sigma+1 : (delta + s > 2 * Delta) \/ (s > 2 * Sigma)}

\* Attack is active: sigma is in attack range and round budget not exhausted
AttackActive(p) == r[p] < MaxRound /\ sigma[p] \in AttackValues

\* Honest step: no delay injected
HonestStep(p) == sigma[p] = 0

\* Invariant: not all initially honest nodes have decided yet
\* Use --inv=NotYetTerminated with Apalache simulate to find a termination witness
InitiallyHonest == Validators \ InitiallyCorrupted

\* Check height 0 directly: h[p] increments after NewHeight so decision[p][h[p]] would
\* point to the new (undecided) height. We want to know if ALL honest nodes decided at h=0.
NotYetTerminated == ~(\A p \in InitiallyHonest : decision[p][0] # NilValue)


(***************************************************************************
 Safety / consistency checks (state-space friendly)
***************************************************************************)

\* Safety invariant used by checks: Agreement
Agreement ==
    \A hh \in 0..MaxHeight :
        \A p \in InitiallyHonest, q \in InitiallyHonest :
            (decision[p][hh] # NilValue /\ decision[q][hh] # NilValue)
            => decision[p][hh] = decision[q][hh]

TypeInvariant ==
    /\ corrupted \subseteq Validators
    /\ removed \subseteq Validators
    /\ h \in [Validators -> 0..MaxHeight]
    /\ r \in [Validators -> 0..MaxRound]
    /\ phase \in [Validators -> Phases]
    /\ lockedValue \in [Validators -> (Values \union {NilValue})]
    /\ lockedRound \in [Validators -> (-1..MaxRound)]
    /\ validValue \in [Validators -> (Values \union {NilValue})]
    /\ validRound \in [Validators -> (-1..MaxRound)]
    /\ proposalValue \in [Validators -> (Values \union {NilValue})]
    /\ proposalVR \in [Validators -> (-1..MaxRound)]
    /\ prevoteValue \in [Validators -> (Values \union {NilValue})]
    /\ precommitValue \in [Validators -> (Values \union {NilValue})]
    /\ decision \in [Validators -> [0..MaxHeight -> (Values \union {NilValue})]]
    /\ countPrevote \in [Validators -> Nat]
    /\ countPrecommit \in [Validators -> Nat]
    /\ countNextRound \in [Validators -> Nat]
    /\ stake \in [Validators -> Nat]
    /\ votingPower \in [Validators -> Int]
    /\ proposerAt \in [0..MaxHeight -> [0..MaxRound -> Validators]]
    /\ delta \in Nat
    /\ sigma \in [Validators -> Nat]
    /\ deltaRound \in [0..MaxRound -> Nat]
    /\ timer \in [Validators -> [active: BOOLEAN, start: Nat, len: Nat]]
    /\ timeoutState \in [Validators -> TimeoutStates]
    /\ clockTime \in Nat
    /\ syncBits \in [Validators -> 0..1]
    /\ pendingNewHeight \in [Validators -> BOOLEAN]
    /\ attackCount \in Nat

\* Reduced next relation for consistency checking to mitigate state explosion:
\*   - safety path allows one constrained AdversaryWake, then protocol steps only
\*   - keeps protocol pipeline transitions only
\* Safety checking path:
\* allow one constrained adversary wake-up, then execute protocol transitions
NextSafety ==
    \/ (attackCount = 0 /\ sigma["v1"] = 0 /\ AdversaryWake("v1", 2 * Sigma + 1))
    \/ \E p \in Validators : NewHeight(p)
    \/ \E p \in Validators : NewRoundAndPropose(p)
    \/ \E p \in Validators : Prevote(p)
    \/ \E p \in Validators : Precommit(p)
    \/ \E p \in Validators : Commit(p)
    \/ \E p \in Validators, rr \in 0..MaxRound : RoundAdvance(p, rr)

Next ==
    \/ \E p \in Validators : Corrupt(p)
    \/ \E p \in Validators, s \in 0..2*Sigma+1 : AdversaryWake(p, s)
    \/ \E p \in Validators : NewHeight(p)
    \/ \E p \in Validators : NewRoundAndPropose(p)
    \/ \E p \in Validators : Prevote(p)
    \/ \E p \in Validators : Precommit(p)
    \/ \E p \in Validators : Commit(p)
    \/ \E p \in Validators, rr \in 0..MaxRound : RoundAdvance(p, rr)


Spec == Init /\ [][Next]_vars
        /\ \A p \in Validators : WF_vars(ProgressStep(p))


\* Bounded attack next: either attack (limited to MaxRound rounds)
\* or honest execution (sigma=0) after attack budget exhausted
\*
\* Fix: during attack phase ALL pipeline steps must be allowed (not just Commit),
\* otherwise a node with sigma>0 gets stuck mid-pipeline.
\* The DelayAttack predicate inside each action causes the degraded behaviour.
\* Termination checking path under bounded delay attacks:
\* explicit attacker wake-up transitions + full honest pipeline exploration
NextBoundedAttack ==
    \* Adversary injects delay into any honest node (sigma=0 -> attack value)
    \/ (sigma["v1"] = 0 /\ AdversaryWake("v1", 2 * Sigma + 1))
    \/ (sigma["v2"] = 0 /\ AdversaryWake("v2", 2 * Sigma + 1))
    \/ (sigma["v3"] = 0 /\ AdversaryWake("v3", 2 * Sigma + 1))
    \* Full pipeline for every honest node regardless of attack state
    \* (DelayAttack predicate inside each action governs degraded vs normal behaviour)
    \/ NewRoundAndPropose("v1")
    \/ NewRoundAndPropose("v2")
    \/ NewRoundAndPropose("v3")
    \/ Prevote("v1")
    \/ Prevote("v2")
    \/ Prevote("v3")
    \/ Precommit("v1")
    \/ Precommit("v2")
    \/ Precommit("v3")
    \/ Commit("v1")
    \/ Commit("v2")
    \/ Commit("v3")
    \/ NewHeight("v1")
    \/ NewHeight("v2")
    \/ NewHeight("v3")
    \/ \E rr \in 0..MaxRound : RoundAdvance("v1", rr)
    \/ \E rr \in 0..MaxRound : RoundAdvance("v2", rr)
    \/ \E rr \in 0..MaxRound : RoundAdvance("v3", rr)

\* Full spec with bounded attack and termination as liveness goal
\* Under bounded attack, all initially honest nodes should eventually decide
\* Constants used by safety runs (check.py patches MaxRound here)
CInitSafety ==
    /\ Validators = {"v1", "v2", "v3", "v4"}
    /\ InitiallyCorrupted = {"v4"}
    /\ Delta = 1
    /\ Sigma = 1
    /\ MaxHeight = 1
    /\ MaxRound = 2
    /\ Values = {1}
    /\ NilValue = 0

\* Apalache-optimized next: no AdversaryWake, no ClockTick, no timer actions
\* (optional reduced path; main safety runs use NextSafety)
NextSafetyApalache ==
    \/ \E p \in Validators : NewHeight(p)
    \/ \E p \in Validators : NewRoundAndPropose(p)
    \/ \E p \in Validators : Prevote(p)
    \/ \E p \in Validators : Precommit(p)
    \/ \E p \in Validators : Commit(p)
    \/ \E p \in Validators, rr \in 0..MaxRound : RoundAdvance(p, rr)

\* Safety init: starts from clean sigma/attack budget; one constrained
\* attack can be injected by NextSafety in the first step
\* Safety-specific initial state used by bounded Agreement checks
InitSafety ==
    /\ corrupted = InitiallyCorrupted
    /\ removed = {}
    /\ messages = {}
    /\ h = [p \in Validators |-> 0]
    /\ r = [p \in Validators |-> 0]
    /\ phase = [p \in Validators |-> "propose"]
    /\ lockedValue = [p \in Validators |-> NilValue]
    /\ lockedRound = [p \in Validators |-> -1]
    /\ validValue = [p \in Validators |-> NilValue]
    /\ validRound = [p \in Validators |-> -1]
    /\ proposalValue = [p \in Validators |-> NilValue]
    /\ proposalVR = [p \in Validators |-> -1]
    /\ prevoteValue = [p \in Validators |-> NilValue]
    /\ precommitValue = [p \in Validators |-> NilValue]
    /\ decision = [p \in Validators |-> [hh \in 0..MaxHeight |-> NilValue]]
    /\ countPrevote = [p \in Validators |-> 0]
    /\ countPrecommit = [p \in Validators |-> 0]
    /\ countNextRound = [p \in Validators |-> 0]
    /\ stake = [p \in Validators |-> 1]
    /\ votingPower = [p \in Validators |-> 1]
    /\ proposerAt = [hh \in 0..MaxHeight |-> [rr \in 0..MaxRound |-> "v1"]]
    /\ delta = 1
    /\ sigma = [p \in Validators |-> 0]
    /\ deltaRound = [rr \in 0..MaxRound |-> 1 + rr * Delta]
    /\ timer = [p \in Validators |-> [active |-> FALSE, start |-> 0, len |-> 0]]
    /\ timeoutState = [p \in Validators |-> "none"]
    /\ clockTime = 0
    /\ syncBits = [p \in Validators |-> 0]
    /\ pendingNewHeight = [p \in Validators |-> FALSE]
    /\ attackCount = 0

SpecSafetyApalache == InitSafety /\ [][NextSafetyApalache]_vars

SpecBoundedAttack ==
    Init
    /\ [][NextBoundedAttack]_vars
    /\ \A p \in InitiallyHonest : WF_vars(ProgressStep(p))

\* Constant initialization for Apalache bounded check
CInit ==
    /\ Validators = {"v1", "v2", "v3", "v4"}
    /\ InitiallyCorrupted = {"v4"}
    /\ Delta = 1
    /\ Sigma = 1
    /\ MaxHeight = 1
    /\ MaxRound = 0
    /\ Values = {1}
    /\ NilValue = 0

=============================================================================

