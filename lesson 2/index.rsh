'reach 0.1'

const Player = {
    getHand: Fun([], UInt),
    seeOutcome: Fun([UInt], Null),
}

export const main = Reach.App(() =>{
    const Alice = Participant('Alice', {
        //specify alice's interact
        ...Player,
        wager: UInt,
    })
    const Bob = Participant('Bob', {
        //specify bob's interact
        ...Player,
        acceptWager: Fun([UInt], Null),
    })
    init()
    //write program here
    Alice.only(() => {
        const amount = declassify(interact.wager);
        const handAlice = declassify(interact.getHand());
    })
    Alice.publish(handAlice, amount)
        .pay(amount)
    commit()

    Bob.only(() => {
        interact.acceptWager(amount);
        const handBob = declassify(interact.getHand())
    })
    Bob.publish(handBob)
        .pay(amount)
    
    const outcome = (handAlice + (4 - handBob)) % 3
    const [forAlice, forBob] =
        outcome == 2 ? [2,0]:
        outcome == 0 ? [0,2]:
                    [1,1];
    transfer(forAlice*amount).to(Alice);
    transfer(forBob*amount).to(Bob);
    commit()

    each ([Alice, Bob], () => {
        interact.seeOutcome(outcome);
    })
})