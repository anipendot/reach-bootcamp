'reach 0.1';

const [ isFingers, ZERO, ONE, TWO, THREE, FOUR, FIVE ] = makeEnum(6);
const [ isGuess, GUESS_ZERO, GUESS_ONE, GUESS_TWO, GUESS_THREE, GUESS_FOUR, GUESS_FIVE, 
  GUESS_SIX, GUESS_SEVEN, GUESS_EIGHT, GUESS_NINE, GUESS_TEN ] = makeEnum(11);
const [ isOutcome, BOB_WINS, DRAW, ALICE_WINS ] = makeEnum(3);

const winner = (aliceFingers, bobFingers, guessA, guessB) => {
  if ( guessA == guessB )
   {
    const outcome = DRAW;
    return outcome;
 } 
 else 
 {
  if ( ((aliceFingers + bobFingers) == guessA ) ) 
  {
    const outcome = ALICE_WINS;
    return outcome;
  }
    else 
    {
      if (  ((aliceFingers + bobFingers) == guessB)) 
      {
        const outcome = BOB_WINS;
        return outcome;
    }
      else 
      {
        const outcome = DRAW;
        return outcome;
      }
 
    }
  }
};

assert(winner(ZERO, TWO, GUESS_ZERO, GUESS_TWO) == BOB_WINS);
assert(winner(TWO, ZERO, GUESS_TWO, GUESS_ZERO) == ALICE_WINS);
assert(winner(ZERO, ONE, GUESS_ZERO, GUESS_TWO) == DRAW);
assert(winner(ONE, ONE, GUESS_ONE, GUESS_ONE) == DRAW);

forall(UInt, aliceFingers =>
  forall(UInt, bobFingers =>
    forall(UInt, guessA =>
      forall(UInt, guessB =>
        assert(isOutcome(winner(aliceFingers, bobFingers, 
          guessA, guessB)))))));

forall(UInt, (aliceFingers) =>
  forall(UInt, (bobFingers) =>
    forall(UInt, (guess) =>
      assert(winner(aliceFingers, bobFingers, guess, 
        guess) == DRAW))));

const Player =
{ ...hasRandom,
  getFingers: Fun([], UInt),
  getGuess: Fun([UInt], UInt),
  seeWinning: Fun([UInt], Null),
  seeOutcome: Fun([UInt], Null),
  informTimeout: Fun([], Null)
};

const Alice =
  { ...Player,
    wager: UInt,
  ...hasConsoleLogger
  };

const Bob =
  {...Player,
    acceptWager: Fun([UInt], Null),
    ...hasConsoleLogger
  };

  const DEADLINE = 30;

  export const main =
  Reach.App(
    {},
    [Participant('Alice', Alice), Participant('Bob', Bob)],
    (A, B) => {
        const informTimeout = () => {
          each([A, B], () => {
            interact.informTimeout(); }); };
      A.only(() => {
        const wager = declassify(interact.wager); });
      A.publish(wager)
        .pay(wager);
      commit();  
 
      B.only(() => {
        interact.acceptWager(wager); });
      B.pay(wager)
        .timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout));

      var outcome = DRAW;
      invariant(balance() == 2 * wager && isOutcome(outcome));

      while (outcome == DRAW) {
        commit();
        A.only(() => {
          const _fingersAlice = interact.getFingers();
          const _guessAlice = interact.getGuess(_fingersAlice);

          const [_commitAlice, _saltAlice] = makeCommitment(interact, _fingersAlice);
          const commitAlice = declassify(_commitAlice);
          const [_guessCommitAlice, _guessSaltAlice] = makeCommitment(interact, _guessAlice);
          const guessCommitAlice = declassify(_guessCommitAlice);
        });

        A.publish(commitAlice).timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout));
        commit();

        A.publish(guessCommitAlice).timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout)); ;
        commit();

        unknowable(B, A(_fingersAlice, _saltAlice));
        unknowable(B, A(_guessAlice, _guessSaltAlice));

        B.only(() => {
          const _fingersBob = interact.getFingers();
          const _guessBob = interact.getGuess(_fingersBob);
          const fingersBob = declassify(_fingersBob);
          const guessBob = declassify(_guessBob);
        });

        B.publish(fingersBob).timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout));
        commit();
        B.publish(guessBob).timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout)); ;

        commit();

        A.only(() => {
          const [saltAlice, fingersAlice] = declassify([_saltAlice, _fingersAlice]);
          const [guessSaltAlice, guessAlice] = declassify([_guessSaltAlice, _guessAlice]);
        });

        A.publish(saltAlice, fingersAlice).timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout));
        checkCommitment(commitAlice, saltAlice, fingersAlice);
        commit();
        
        A.publish(guessSaltAlice, guessAlice).timeout(relativeTime(DEADLINE), () => closeTo(B, informTimeout));
        checkCommitment(guessCommitAlice, guessSaltAlice, guessAlice);
        commit();

        A.only(() => {
          const WinningNumber = fingersAlice + fingersBob;
          interact.seeWinning(WinningNumber);
        });

        A.publish(WinningNumber).timeout(relativeTime(DEADLINE), () => closeTo(A, informTimeout));

        outcome = winner(fingersAlice, fingersBob, guessAlice, guessBob);
        continue;
      }

      assert(outcome == ALICE_WINS || outcome == BOB_WINS);
      transfer(2*wager).to(outcome == ALICE_WINS ? A : B);
      commit();
      each([A, B], () => {
        interact.seeOutcome(outcome); })
        exit(); });