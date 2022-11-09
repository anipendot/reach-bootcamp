'reach 0.1';

const [gameOutcome, ALICE_WINS, BOB_WINS, DRAW] = makeEnum(3);

const winner = (playHandA, playHandB, gHandA, gHandB) => {

  if (gHandA == gHandB) {
    return DRAW;
  } else {
    if (gHandA == (playHandA + playHandB)) {
      return ALICE_WINS;
    } else {
      if (gHandB == (playHandA + playHandB)) {
        return BOB_WINS;
      } else {
        return DRAW;
      }
    }
  }
};

assert(winner(0, 4, 0, 4) == BOB_WINS);
assert(winner(4, 0, 4, 0) == ALICE_WINS);
assert(winner(0, 1, 0, 4) == DRAW);
assert(winner(5, 5, 5, 5) == DRAW);

forall(UInt, playHandA =>
  forall(UInt, playHandB =>
    forall(UInt, gHandA =>
      forall(UInt, gHandB =>
        assert(gameOutcome(winner(playHandA, playHandB, gHandA, gHandB)))))));

forall(UInt, playHandA =>
  forall(UInt, playHandB =>
    forall(UInt, sameGuess => 
      assert(winner(playHandA, playHandB, sameGuess, sameGuess) == DRAW))));

const Player = {
  ...hasRandom, 
  getHand: Fun([], UInt),
  getGuess: Fun([UInt], UInt),
  seeOutcome: Fun([UInt], Null),
  informTimeout: Fun([], Null),
};

// REACH BEGINS!!!
export const main = Reach.App(() => {

  const Alice = Participant('Alice', {
    ...Player, 
    wager: UInt, 
    deadline: UInt,
  });

  const Bob = Participant('Bob', {
    ...Player,
    acceptWager: Fun([UInt], Null),
  });

  init();

  const informTimeout = () => {
    each([Alice, Bob], () => {
      interact.informTimeout();
    });
  };

  Alice.only(() => {
    const wager = declassify(interact.wager);
    const deadline = declassify(interact.deadline);
  });

  Alice.publish(wager, deadline)
    .pay(wager);
  commit();

  Bob.only(() => {
    interact.acceptWager(wager);
  });

  Bob.pay(wager)
    .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout));

  var outcome = DRAW;

  invariant(balance() == 2 * wager && gameOutcome(outcome));

  while ( outcome == DRAW ) {
    commit();

    Alice.only(() => {
      const _playHandA = interact.getHand();
      const _gHandA = interact.getGuess(_playHandA);

      const [_commitA, _saltA] = makeCommitment(interact, _playHandA);
      const commitA = declassify(_commitA);
      const [_guessCommitA, _guessSaltA] = makeCommitment(interact, _gHandA);
      const guessCommitA = declassify(_guessCommitA);
    });

    Alice.publish(commitA, guessCommitA)
      .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
    commit();

    unknowable(Bob, Alice(_playHandA, _saltA));
    unknowable(Bob, Alice(_gHandA, _guessSaltA));

    Bob.only(() => {
      const _playHandB = interact.getHand();
      const _gHandB = interact.getGuess(_playHandB);
      const playHandB = declassify(_playHandB);
      const gHandB = declassify(_gHandB);
    });

    Bob.publish(playHandB, gHandB)
      .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout));
    commit();

    Alice.only(() => {
      const [saltA, playHandA] = declassify([_saltA, _playHandA]);
      const [guessSaltA, gHandA] = declassify([_guessSaltA, _gHandA]);
    });

    Alice.publish(saltA, playHandA, guessSaltA, gHandA)
      .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
    checkCommitment(commitA, saltA, playHandA);
    checkCommitment(guessCommitA, guessSaltA, gHandA);

    outcome = winner(playHandA, playHandB, gHandA, gHandB);
    continue;
  }; 


  assert(outcome == ALICE_WINS || outcome == BOB_WINS);

  transfer(2 * wager).to(outcome == ALICE_WINS ? Alice : Bob);
  commit();

  each([Alice, Bob], () => {
    interact.seeOutcome(outcome);
  });
  exit();
});

//Updated 11/11