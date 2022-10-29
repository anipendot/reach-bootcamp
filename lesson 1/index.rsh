'reach 0.1'

const Player = {
    getHand: Fun([], UInt),
    seeOutcome: Fun([UInt], Null),
}

export const main = Reach.App(() =>{
    const Alice = Participant('Alice', {
        //specify alice's interact
        ...Player,
    })
    const Bob = Participant('Bob', {
        //specify bob's interact
        ...Player,
    })
    init()
    //write program here
    Alice.only(() => {
        const handAlice = declassify(interact.getHand())
    })
    Alice.publish(handAlice)
    commit()

    Bob.only(() => {
        const handBob = declassify(interact.getHand())
    })
    Bob.publish(handBob)
    const outcome = (handAlice + (4 - handBob)) % 3
    commit()

    each ([Alice, Bob], () => {
        interact.seeOutcome(outcome);
    })
})