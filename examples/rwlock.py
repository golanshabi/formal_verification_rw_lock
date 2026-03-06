class ReaderThread(Expr): ...

class WriterThread(Expr): ...

class RWLockSystem(TransitionSystem):
    # Readers state
    pc1: Rel[ReaderThread]
    pc2: Rel[ReaderThread]
    pc3: Rel[ReaderThread]

    # Writers state
    pc4: Rel[WriterThread]
    pc5: Rel[WriterThread]
    pc6: Rel[WriterThread]
    
    Rscheduled : Rel[ReaderThread]
    Wscheduled : Rel[WriterThread]

    writer_in: Bool

    @init
    def initial(self, R: ReaderThread, W: WriterThread) -> BoolRef:
        return And(
            self.pc1(R),
            Not(self.pc2(R)),
            Not(self.pc3(R)),
            self.pc4(W),
            Not(self.pc5(W)),
            Not(self.pc6(W)),
        )

    @transition
    def step12(self, r: ReaderThread) -> BoolRef:
        R = ReaderThread("R")
        W = WriterThread("W")
        return And(
            # guard
            self.pc1(r),
            # A helper method to change a function or relation
            # for specific elements:
            self.pc1.update({(r,): false}),
            self.pc2.update({(r,): true}),
            # A helper method to make pre- and post-state identical:
            self.pc3.unchanged(),
            self.pc4.unchanged(),
            self.pc5.unchanged(),
            self.pc6.unchanged(),
            # fairness
            ForAll(R, self.Rscheduled(R) == (R == r)),
            ForAll(W, Not(self.Wscheduled(W))),
        )  # </>

    @transition
    def step22(self, r: ReaderThread) -> BoolRef:
        R = ReaderThread("R")
        W = WriterThread("W")
        return And(
            # guard
            self.pc2(r),
            writer_in == true,
            # updater
            self.pc2.unchaged(),
            self.pc3.unchaged(),
            self.pc4.unchaged(),
            self.pc5.unchaged(),
            self.pc6.unchaged(),
            self.writer_in.unchaged(),
            # fairness
            ForAll(R, self.Rscheduled(R) == (R == r)),
            ForAll(W, Not(self.Wscheduled(W))),
        )

    @transition
    def step23(self, r: ReaderThread) -> BoolRef:
        R = ReaderThread("R")   
        W = WriterThread("W")
        return And(
            # guard
            self.pc2(r),
            writer_in == false,
            # updater
            self.pc1.unchanged(),
            self.pc2.update({(r,): false}),
            self.pc3.update({(r,): true}),
            self.pc4.unchanged(),
            self.pc5.unchanged(),
            self.pc6.unchanged(),
            self.writer_in.unchanged(),
            # fairness
            ForAll(R, self.Rscheduled(R) == (R == r)),
            ForAll(W, Not(self.Wscheduled(W))),
        )
    
    @transition
    def step31(self, r: ReaderThread) -> BoolRef:
        R = ReaderThread("R")
        W = WriterThread("W")
        return And(
            # guard
            self.pc3(r),
            # updater
            self.pc1.update({(r,): true}),
            self.pc2.unchanged(),
            self.pc3.update({(r,): false}),
            self.pc4.unchanged(),
            self.pc5.unchanged(),
            self.pc6.unchanged(),
            self.writer_in.unchanged(),
            # fairness
            ForAll(R, self.Rscheduled(R) == (R == r)),
            ForAll(W, Not(self.Wscheduled(W))),
        )

    @transition
    def step45(self, w: WriterThread) -> BoolRef:
        W = WriterThread("W")
        R = ReaderThread("R")
        return And(
            # guard
            self.pc4(w),
            # updater
            self.pc1.unchanged(),
            self.pc2.unchanged(),
            self.pc3.unchanged(),
            self.pc4.update({(w,): false}),
            self.pc5.update({(w,): true}),
            self.pc6.unchanged(),
            self.writer_in.update(true),
            # fairness
            ForAll(R, Not(self.Rscheduled(R))),
            ForAll(W, self.Wscheduled(W) == (W == w)),
        )

    @transition
    def step56(self, w: WriterThread) -> BoolRef:
        W = WriterThread("W")
        R = ReaderThread("R")
        return And(
            # guard
            self.pc5(w),
            ForAll(R, Not(self.pc3(R))),
            # updater
            self.pc1.unchanged(),
            self.pc2.unchanged(),
            self.pc3.unchanged(),
            self.pc4.update({(w,): false}),
            self.pc5.update({(w,): true}),
            self.pc6.unchanged(),
            self.writer_in.unchanged(),
            # fairness
            ForAll(R, Not(self.Rscheduled(R))),
            ForAll(W, self.Wscheduled(W) == (W == w)),
        )
    
    @transition
    def step64(self, w: WriterThread) -> BoolRef:
        W = WriterThread("W")
        R = ReaderThread("R")
        return And(
            # guard
            self.pc6(w),
            # updater
            self.pc1.unchanged(),
            self.pc2.unchanged(),
            self.pc3.unchanged(),
            self.pc4.update({(w,): true}),
            self.pc5.unchanged(),
            self.pc6.update({(w,): false}),
            self.writer_in.update(false),
            # fairness
            ForAll(R, Not(self.Rscheduled(R))),
            ForAll(W, self.Wscheduled(W) == (W == w)),
        )

# <>
# | ### Temporal Property
# | Once the system is defined, we can write temporal properties for it
# | by extending the `Prop` class.
# | The temporal property is given by the `prop` method.
# | Within the temporal property,
# | we can freely use the temporal operators `G` and `F`.
class RWLockProp(Prop[RWLockSystem]):
    def prop(self) -> BoolRef:
        R = ReaderThread("R")
        W = WriterThread("W")
        return Implies(
            And(
                ForAll(R, G(F(self.sys.Rscheduled(R)))), # every reader is scheduled infinitely often
                ForAll(W, G(F(self.sys.Wscheduled(W)))), # every writer is scheduled infinitely often
            ),
            And(
                ForAll(
                    R,
                    G(
                        Implies(
                            self.sys.pc2(R),
                            F(self.sys.pc3(R)),
                        )
                    ),
                ), # every reader in pc2 is eventually in pc3
                ForAll(
                    W,
                    G(
                        Implies(
                            self.sys.pc5(W),
                            F(self.sys.pc6(W)),
                        )
                    ),
                ), # every writer in pc5 is eventually in pc6
            ), # every reader is scheduled infinitely often and every writer is scheduled infinitely often
               # imply that every reader in pc2 is eventually in pc3 and every writer in pc5 is eventually in pc6
        )  # </>
