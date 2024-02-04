Jakub - Throughout the number theory side of the code (2nd half) I have left fairly detailed dated comments about what I was doing at particular times during the project. I have also labelled individual theorems or parts of theorems that I have proved, so my contribution to the project can be easily seen. I committed to the github repository very frequently, often several times per day, which was far more than others in my group, but this does not mean at all that I have contributed more to the project, so please take this into account.

Katie - Starting off slow, I got to grips with both the coding and LEAN-specific programming through proving basic lemmas about coprimality, working up to Euclid's lemma. I learnt a lot from this, including many logic tactics that would have certainly reduced this section into just a few lemmas. I think my immediate improvement (i.e. results about the totient function and onwards) is clear, and so, while this section was not utilised in any major final theorems, it was vital to my practise in independent LEAN formalisation. After term started up again, it proved much easier to collaborate efforts towards a main goal with Jakub: after realising it was too difficult of a task for the Group Theory team to feasibly manage, I began to research into Mathlib's method of working up to Euler's totient theorem, and ruling out what we reasonably could or couldn't replicate independently. We came to an agreement that using the definitiion ZMod.val and a few smaller lemmas about ZMod.val - as well as some generic Fintype/set.card results - would keep the formalisation interesting and fun, but still challenging. I independently created a workaround to equate the Fintype.card and Finset.card components in order to formalise 'totient_eq_zmod_units_card', and spelled out the stepping stones towards the overall proof of how we could connect everything (from coprime lemmas, to modular inverses) on paper. At first it was hard working out what exactly we would need for the "crown jewel" isomorphism between Units (ZMod n) and {x // x ∈ (Finset.range n).filter n.Coprime}, since we were working with Jakub's inverse definition and I didn't know how many coersion and equating lemmas we would need in the end. When this became the final result we needed to prove, it was a great team effort to first of all understand the isomorphism creation and then to replicate it for our own (slightly different, but enough difference for LEAN to require a few extra days/weeks of conviction) fintypes. After this, it was clear that a great deal of our theorems were simply unneeded for the main result (albeit some crop up in surprising ways). Still, many of them offer a demonstration of skill that felt satisfying to build up to, and so I am reluctant to erase them in pursuit of a concise document. Fintype and Finset equivalence (as well as casting between norms) proved to be a consistent bane of my efforts, including trying to bring so many of our major results together to prove Wilson's Theorem. If I had started this earlier, I think it would have been possibly doable with a work-around method that fresh eyes would have spotted. Outside of my code, a lot of my efforts went into organising meet-ups - to ensure everyone was on the same page - and the aforementioned planning of structure for proving Euler's totient theorem. Unfortunately, I hadn't realised how clueless I was at committing through VSCode with a GitHub extension until returning for term 2 and finding that I was not synced with the master branch at all. Jakub (and sometimes Rose) helped a lot during times where it would take almost an hour each day to commit and sync - something that is especially tedious on Mac, for some reason. As of today, I can say I can commit without fault about 95% of the time :). What was once a demotivating reflection of very gradual skill gain, is now a satisfying rollercoaster of understanding the efforts that go into each part of formalisation, and I feel more than content towards my improvements over the course of this project, which is on top of a by-product of general developments in my logic skills.
