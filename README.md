Jakub - Throughout the number theory side of the code (2nd half) I have left fairly detailed dated comments about what I was doing at particular times during the project. I have also labelled individual theorems or parts of theorems that I have proved, so my contribution to the project can be easily seen. I committed to the github repository very frequently, often several times per day, which was far more than others in my group, but this does not mean at all that I have contributed more to the project, so please take this into account. I am very happy with my improvements as a LEAN user (LEANer? LEANist?) during the project, throughout the duration of the project I have been consistently improving my formalisation abilities such as formal rigour in proofs, tactic vocabulary and understanding some of the intricacies and quirks of LEAN; from my initial naïve attempts to use for loops to define my euclidean algorithm I feel like after every big proof my LEANing abilities have significantly improved. Looking back at my early code (most of the stuff from 2023), there is a clear lack of understanding of what would be required to prove Bézout's lemma, and the methods i used were restrictive, for example it took me a long time to learn to make good use of the `have` tactic (which has since become one of my favourites). The difference in my ability from the outset of the project is clear to see, not even from the aforementioned for loops, but for instance see the difference between an early theorem `bez_rec`, which took me days to prove, and something later like `zmod_mul_inv_eq_one_iff_coprime_n`, `my_zmod_unitsEquivCoprime` or `sum_nat` (though on that last one I didn't have nearly as much time as I wanted to tidy it up). Maybe the difference is less obvious to those with vastly better LEANing ability, but to me it is night and day. I believe that learning how to use LEAN has greatly improved my rigour and logic when it comes to mathematical proof, it would not be an exaggeration to say that it has changed the way I think about proof in general. I think that LEAN abiliy will be a great asset for the future of my mathematical career, though it is often difficult and painful to work with, finally completing a big proof is a very rewarding feeling, and I am glad to have experienced it. Outside LEAN, I was quick to pick up how to use the repository, after Rose taught me, and after only a few botched commits and lake installs in November, I was the one helping others with using the website. Since November I have been working on the project off and on, unfortunately the group were not able to get as much as we would have liked completed over the holidays due to illness and family events, and most of our LEANing abilities were poor at best before the holidays that any progress at that time was extremely slow. This term, especially these past few weeks (evidently the looming deadline was a big incentive), we have been consistently working collaboratively to try to complete our initial goals, which Katie and I on the number theory side managed to do just a few days before the end of the project on 04/02/24 (today).

Katie - Starting off slow, I got to grips with both the coding and LEAN-specific programming through proving basic lemmas about coprimality, working up to Euclid's lemma. I learnt a lot from this, including many logic tactics that would have certainly reduced this section into just a few lemmas. I think my immediate improvement (i.e. results about the totient function and onwards) is clear, and so, while this section was not utilised in any major final theorems, it was vital to my practise in independent LEAN formalisation. After term started up again, it proved much easier to collaborate efforts towards a main goal with Jakub: after realising it was too difficult of a task for the Group Theory team to feasibly manage, I began to research into Mathlib's method of working up to Euler's totient theorem, and ruling out what we reasonably could or couldn't replicate independently. We came to an agreement that using the definition `ZMod.val` and a few smaller lemmas about `ZMod.val` - as well as some generic `Fintype/set.card` results - would keep the formalisation interesting and fun, but still challenging. I independently created a workaround to equate the Fintype.card and Finset.card components in order to formalise `totient_eq_zmod_units_card`, and spelled out the stepping stones towards the overall proof of how we could connect everything (from coprime lemmas, to modular inverses) on paper. At first it was hard working out what exactly we would need for the "crown jewel" isomorphism between `Units (ZMod n)` and `{x // x ∈ (Finset.range n).filter n.Coprime}`, since we were working with Jakub's inverse definition and I didn't know how many coersion and equating lemmas we would need in the end. When this became the final result we needed to prove, it was a great team effort to first of all understand the isomorphism creation and then to replicate it for our own (slightly different, but enough difference for LEAN to require a few extra days/weeks of conviction) fintypes. After this, it was clear that a great deal of our theorems were simply unneeded for the main result (albeit some crop up in surprising ways). Still, many of them offer a demonstration of skill that felt satisfying to build up to, and so I am reluctant to erase them in pursuit of a concise document. Fintype and Finset equivalence (as well as casting between norms) proved to be a consistent bane of my efforts, including trying to bring so many of our major results together to prove Wilson's Theorem. If I had started this earlier, I think it would have been possibly doable with a work-around method that fresh eyes would have spotted. Outside of my code, a lot of my efforts went into organising meet-ups - to ensure everyone was on the same page - and the aforementioned planning of structure for proving Euler's totient theorem. Unfortunately, I hadn't realised how clueless I was at committing through VSCode with a GitHub extension until returning for term 2 and finding that I was not synced with the master branch at all. Jakub (and sometimes Rose) helped a lot during times where it would take almost an hour each day to commit and sync - something that is especially tedious on Mac, for some reason. As of today, I can say I can commit without fault about 95% of the time `:)`. What was once a demotivating reflection of very gradual skill gain, is now a satisfying rollercoaster of understanding the efforts that go into each part of formalisation, and I feel more than content towards my improvements over the course of this project, which is on top of a by-product of general developments in my logic skills.

Edward - I started off this project working with Rose outlining what we were going to do for groups. She wrote down the statements of the basic lemmas for groups and I got to grips filling in all the proofs, which helped me get to grips with the basics of proof. After this I replicated exactly what I'd done for additivie groups as well as extended it to Rings. This progress was slow, but I gained confidence writing statements as well as being able to write definitions. The Rings aspect wasn't used in the end, as we didn't need the direct product of rings in the end like initially thought. During this time Rose was developing code for cosets and from here I was tasked to create a definition of quotient groups. My original definition used the notion of a quotient baked into lean. From here I realised to create any meaningful connection between quotient groups and cosets I would need to show that Left and Right cosets being equal implies normality. I ended up looking in Mathlib for inspiration to provide a rough structure for the proof. Although this gave me an idea of what theorems and lemmas to prove first, ultimately Mathlib didn't prove much more useful. To prove these statements took a great deal of headbanging and represented a serious step up in difficulty compared to what I'd been working with before. In the end I managed to prove `NormalIffEqMulCosets`, but not without encountering various other obstacles that needed to be overcome by adding more proofs such as `MemLeftCoset`. One thing one quickly discovers about Lean is that what often appears to be a simple challenge is often far bigger than one thinks. In the end I actually had to end up changing the quotient definition - creating left and right quotient group based definitions, as well as a statement to show they are in fact the same. For the old definition I still needed to show it was equivalent to the set of left cosets for Roses part of the project, and although I tried very hard to make this possible, it seemed very much beyond my abilities. As a result I decided to directly make the left and right quotient groups. Some aspects of my code didn't end up being fully utilised, that is ultimately sometimes what happens with an undertaking as big as this. However, overall I feel like my abilities with Lean have only gotten stronger as the term went on and I'm happy to see the improvement I've made, with recent contributions feeling as though they'd have been impossible for me to make in term 1.