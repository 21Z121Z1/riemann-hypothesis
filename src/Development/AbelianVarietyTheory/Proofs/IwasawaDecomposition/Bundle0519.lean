import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0514
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0400
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0110
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0345
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0512
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSideReadingLevelZeroMoved
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.GoodSideLattices

open NumberField IsDedekindDomain

def locMeet {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V] {ι : Type}
    (P : ι → HeightOneSpectrum (𝓞 K)) (S : ι → Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {x | ∀ w, ∃ d : 𝓞 K, d ∉ (P w).asIdeal ∧ d • x ∈ S w}
  zero_mem' := fun w => ⟨1, fun h => (P w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  add_mem' := by
    intro x y hx hy w
    obtain ⟨a, ha, hax⟩ := hx w
    obtain ⟨b, hb, hby⟩ := hy w
    refine ⟨a * b, fun h => ?_, ?_⟩
    · rcases (P w).isPrime.mem_or_mem h with h | h
      exacts [ha h, hb h]
    · rw [smul_add]
      refine (S w).add_mem ?_ ?_
      · rw [mul_comm, mul_smul]
        exact (S w).smul_mem _ hax
      · rw [mul_smul]
        exact (S w).smul_mem _ hby
  smul_mem' := by
    intro c x hx w
    obtain ⟨a, ha, hax⟩ := hx w
    exact ⟨a, ha, by rw [smul_comm]; exact (S w).smul_mem c hax⟩

theorem mem_locMeet {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V] {ι : Type}
    (P : ι → HeightOneSpectrum (𝓞 K)) (S : ι → Submodule (𝓞 K) V) (x : V) :
    x ∈ locMeet P S ↔ ∀ w, ∃ d : 𝓞 K, d ∉ (P w).asIdeal ∧ d • x ∈ S w := Iff.rfl

theorem majAt_cast {K : Type} [Field K] [NumberField K] [StarRing K] {a b : ℕ} (h : a = b)
    (M : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ) (M' : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (v : InfinitePlace K)
    (hM : M' v = (M v).submatrix (Fin.cast h) (Fin.cast h)) (x y : Fin b → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin a)) M' v (x ∘ Fin.cast h) (y ∘ Fin.cast h) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin b)) M v x y := by
  subst h
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord]
  rw [hM]
  rfl

end GlobalTheory.Mem.R3.Rw.GoodSideLattices

namespace GlobalTheory.Mem.R3.Rw.GoodSideLattices

set_option maxHeartbeats 1000000 in

theorem reading_level_zero_of_side_data {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (hP : Pins R F cG) (hH : Holds R F) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (y : Hd R.toRealDat)
    {E1 : Hs} (jE1 : E1.T →ₗ[ℂ] (y.C F.lv2).Amb 0) (n1 : ℕ) (c1 : Module.Basis (Fin n1) ℂ E1.T)
    (Xo1 : InfinitePlace D.what₂.LL → Matrix (Fin n1) (Fin n1) ℂ) (h1 : RrT F y true jE1 n1 c1 Xo1)
    (ε1 : D.div.RR.V ≃ₗ[D.what₂.LL] (Fin n1 → D.what₂.LL))
    (j1 : ∀ x, HEq (Y.Ish.jE (D.jEE x)).1 (jE1 (∑ i, D.what₂.embLL (ε1 x i) • c1 i)))
    (m1 : ∀ v, v ≠ A3.A.v0 → ∀ x x', Formalism.HermitianLatticesTheory.majAt D.div.RR.b D.div.RR.X v x x' =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL (Fin n1)) Xo1 v (ε1 x) (ε1 x'))
    {E0 : Hs} (heq_eigen_embedding_zero : E0.T →ₗ[ℂ] (y.C F.lv2).Amb 0) (n0 : ℕ) (c0 : Module.Basis (Fin n0) ℂ E0.T)
    (Xo0 : InfinitePlace D.what₂.LL → Matrix (Fin n0) (Fin n0) ℂ) (h0 : RrT F y false heq_eigen_embedding_zero n0 c0 Xo0)
    (ε0 : X0.s.RR.V ≃ₗ[D.what₂.LL] (Fin n0 → D.what₂.LL))
    (j0 : ∀ x, HEq (Y.Iz.jE (X0.s.jEE x)).1 (heq_eigen_embedding_zero (∑ i, D.what₂.embLL (ε0 x i) • c0 i)))
    (m0 : ∀ v, v ≠ A3.A.v0 → ∀ x x', Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X v x x' =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL (Fin n0)) Xo0 v (ε0 x) (ε0 x'))
    (rr : (RowSide.sharp D).RRDef) (rr0 : X0.s.RRDef) : Nonempty (RationalReadingWithoutCongruence R F X0 Y) := by
  obtain ⟨jW, hjW⟩ := GlobalTheory.Mem.CoordW.exists_jW D G Pl0 I0 T A3 Ks R F cG hP hH Y.mj
  obtain ⟨rfl, a1, b1⟩ := h1
  obtain ⟨rfl, a0, b0⟩ := h0
  refine ⟨⟨ε1.symm, ε0.symm, fun x => ?_, fun x => ?_, fun v hv x x' => ?_, fun v hv x x' => ?_, rr, rr0, jW, hjW⟩⟩
  · have h := j1 (ε1.symm x)
    rw [ε1.apply_symm_apply] at h
    exact (eq_of_heq h).trans (a1 x)
  · have h := j0 (ε0.symm x)
    rw [ε0.apply_symm_apply] at h
    exact (eq_of_heq h).trans (a0 x)
  · rw [m1 v hv, ε1.apply_symm_apply, ε1.apply_symm_apply]
    exact majAt_cast rfl _ Xo1 v (b1 v).1 x x'
  · rw [m0 v hv, ε0.apply_symm_apply, ε0.apply_symm_apply]
    exact majAt_cast rfl _ Xo0 v (b0 v).1 x x'

theorem exists_hlat {K : Type} [Field K] [NumberField K] [StarRing K] (e : K →+* ℂ) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (c : Module.Basis (Fin n) ℂ W) (Xo : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hXo : ∀ v, IsUnit (Xo v).det) {ι : Type} (P : ι → HeightOneSpectrum (𝓞 K)) (S : ι → Set W) :
    ∃ (RR : HLat K) (j : RR.V →ₛₗ[e] W) (ε : RR.V ≃ₗ[K] (Fin n → K)), (∀ v, IsUnit (RR.X v).det) ∧
      (LinearIndependent ℂ (fun i => j (RR.b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (RR.b i))) = ⊤) ∧
      (∀ x : RR.V, Formalism.HermitianLatticesTheory.normAt RR.b RR.X (InfinitePlace.mk e) x = ‖j x‖) ∧ (∀ x, j x = ∑ i, e (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk e → ∀ x x', Formalism.HermitianLatticesTheory.majAt RR.b RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : RR.V, x ∈ RR.L ↔ ∀ u, ∃ d : 𝓞 K, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 K) {z | j z ∈ S u} := by
  classical
  obtain ⟨Xf, hXf, hXfn⟩ := GlobalTheory.exists_frames_normAt_eq_norm K e W n c ⊤
  let X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ := fun v => if v = InfinitePlace.mk e then Xf v else Xo v
  refine ⟨{ V := Fin n → K, ι := Fin n, b := Pi.basisFun K (Fin n), X := X,
            L := locMeet P fun u => Submodule.span (𝓞 K) {z | GlobalTheory.Mem.coordForm e c z ∈ S u} },
    GlobalTheory.Mem.coordForm e c, LinearEquiv.refl _ _, fun v => ?_, ?_, fun x => ?_, fun _ => rfl, fun v hv x x' => ?_, fun _ => Iff.rfl⟩
  · show IsUnit (if v = InfinitePlace.mk e then Xf v else Xo v).det
    split_ifs
    exacts [hXf v, hXo v]
  · have : (fun i => GlobalTheory.Mem.coordForm e c (Pi.basisFun K (Fin n) i)) = c := funext (GlobalTheory.Mem.coordForm_basisFun e c)
    show LinearIndependent ℂ (fun i => GlobalTheory.Mem.coordForm e c (Pi.basisFun K (Fin n) i)) ∧
      Submodule.span ℂ (Set.range (fun i => GlobalTheory.Mem.coordForm e c (Pi.basisFun K (Fin n) i))) = ⊤
    rw [this]
    exact ⟨c.linearIndependent, c.span_eq⟩
  · refine Eq.trans ?_ (hXfn x)
    show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X _ x = _
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_true]
  · show Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x' = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) Xo v x x'
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, X, if_neg hv]

end GlobalTheory.Mem.R3.Rw.GoodSideLattices

namespace GlobalTheory.Mem.R3.Rw.GoodSideLattices

@[reducible] def reRow {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)
    (cen : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) →ₐ[ℂ] Module.End ℂ (S.Amb μ))
    (tie : ∀ μ, S.eOp μ = (open Classical in
      if h : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) then cen μ ⟨D.ntypes.e0, h⟩ else 0))
    (RR : HLat D.what₂.LL) (fr : ∀ v, IsUnit (RR.X v).det) (j : RR.V →ₛₗ[D.what₂.embLL] EE)
    (bs : LinearIndependent ℂ (fun i => j (RR.b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (RR.b i))) = ⊤)
    (nm : ∀ x : RR.V, Formalism.HermitianLatticesTheory.normAt RR.b RR.X (InfinitePlace.mk D.what₂.embLL) x = ‖j x‖) : RowSide D EE :=
  { S with cen := cen, eOp_tie := tie, RR := RR, RR_frames := fr, jEE := j, jEE_basis := bs, jEE_norm := nm }

theorem RRset_reRow {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)
    (cen tie RR fr j bs nm) (μ : D.what₂.Tup) : (reRow S cen tie RR fr j bs nm).RRset μ = S.RRset μ := by
  have h : ∀ k, (reRow S cen tie RR fr j bs nm).downTo μ k = S.downTo μ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => exact congrArg (fun φ => φ.comp (S.io μ k)) ih
  have hi : (reRow S cen tie RR fr j bs nm).iota μ = S.iota μ :=
    congrArg (fun φ => (S.multZero μ).toLinearEquiv.toLinearMap ∘ₗ φ ∘ₗ (S.multTop μ).symm.toLinearEquiv.toLinearMap) (h D.R.m)
  exact congrArg (fun φ : S.Amb μ →ₗ[ℂ] EE => φ '' ((fun x => (S.V0 μ ⊓ (S.V0 μ ⊓ LinearMap.ker φ)ᗮ).starProjection x) ''
    ((S.Mtilde μ).carrier ∩ (S.V0 μ : Set (S.Amb μ))))) hi

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over}

set_option maxHeartbeats 1000000 in
theorem RRset_side (s s' : Side0 o) (μ : (w.D o.Z).what₂.Tup) : s.p0.s.RRset μ = s'.p0.s.RRset μ :=
  RRset_reRow s'.p0.s s.cen s.tie s.RR s.frames s.jEE s.basis s.norm μ

set_option maxHeartbeats 1000000 in

theorem eq_of_stdIso (m : Moved o) (eR : Gc B w.px ≃* G0g (w.D o.Z).nd) (hR : StdIso (w.st o.Z) w.px eR) :
    m.z.R.eG.trans m.z.cG = eR := by
  obtain ⟨plg, iso, h1, h2⟩ := hR
  obtain ⟨plg₀, iso₀, k1, -, -, k2⟩ := m.z.pins.keep.grp
  refine MulEquiv.ext fun g => funext fun kv => ?_
  exact (Bare.read_unique g (m.z.R.eG g) (m.z.idG g) (plg kv) (plg₀ kv) ((h1 kv).trans (k1 kv).symm) (iso kv) (iso₀ kv)
    (h2 g kv) (k2 g kv)).symm

set_option maxHeartbeats 1000000 in

theorem exists_side (hF : o.Fits) (m : Moved o) {n : ℕ} (c : Module.Basis (Fin n) ℂ (q.p.ch false).EE.T)
    (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ) (hXo : ∀ v, IsUnit (Xo v).det) {ι : Type}
    (P : ι → HeightOneSpectrum (𝓞 B.LL)) (S : ι → Set (q.p.ch false).EE.T) :
    ∃ (s : Side0 o) (ε : s.RR.V ≃ₗ[B.LL] (Fin n → B.LL)), (∀ x, s.jEE x = ∑ i, B.embLL (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk B.embLL → ∀ x x', Formalism.HermitianLatticesTheory.majAt s.RR.b s.RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin n)) Xo v (ε x) (ε x')) ∧
      ∀ x : s.RR.V, x ∈ s.RR.L ↔ ∀ u, ∃ d : 𝓞 B.LL, d ∉ (P u).asIdeal ∧ d • x ∈ Submodule.span (𝓞 B.LL) {z | s.jEE z ∈ S u} := by
  obtain ⟨RR, j, ε, h1, h2, h3, h4⟩ := exists_hlat B.embLL c Xo hXo P S
  let eR₀ : Gc B w.px ≃* G0g (w.D o.Z).nd := m.z.R.eG.trans m.z.cG
  have hc : (w.D o.Z).ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D o.Z).nd)) := hF.grpAt.cen
  refine ⟨⟨fun μ => (q.p.sA false μ).act.comp (Bare.cenPull eR₀), fun μ => ?_, fun eR hR μ a a' ha x => ?_, RR, h1, j, h2, h3⟩, ε, h4⟩
  · rw [dif_pos hc]
    exact Bare.e_eq_act (m.t.tA false μ) (m.t.lawsA false μ) (Bare.cenPull eR₀ ⟨_, hc⟩) fun g =>
      (m.z.good.2 g).trans (Bare.coeff_cenPull eR₀ ⟨_, hc⟩ g).symm
  · have he : eR₀ = eR := eq_of_stdIso m eR hR
    subst he
    exact congrArg (fun z => (q.p.sA false μ).act z x) (Bare.cenPull_eq _ ha)

end GlobalTheory.Mem.R3.Rw.GoodSideLattices

namespace GlobalTheory.Mem.R3.Rw.GoodSideLattices

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over}

def Good (m : Moved o) (s : Side0 o) : Prop :=
  ∃ (n : ℕ) (c : Module.Basis (Fin n) ℂ (q.p.ch false).EE.T) (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ)
    (ε : s.RR.V ≃ₗ[B.LL] (Fin n → B.LL)), RrT m.z.F m.y false (m.t.ch false).jE n c Xo ∧
      (∀ x, s.jEE x = ∑ i, B.embLL (ε x i) • c i) ∧
      (∀ v, v ≠ InfinitePlace.mk B.embLL → ∀ x x', Formalism.HermitianLatticesTheory.majAt s.RR.b s.RR.X v x x' =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL (Fin n)) Xo v (ε x) (ε x')) ∧ s.p0.s.RRDef

set_option maxHeartbeats 1000000 in
theorem exists_good (hF : o.Fits) (m : Moved o) : ∃ s : Side0 o, Good m s := by
  obtain ⟨n, c, Xo, h⟩ := rrT_exists (w.st o.Z).toD7 (Gc B w.px) (PlS B w.px) (PlI B w.px) (TupU w.I (usedOf w.I T Wt))
    (famR (w.st o.Z) w.I hX (usedOf w.I T Wt) m.z.Xg m.z.tr) m.z.core.Q.c.F m.z.R m.z.F m.z.cG m.z.pins m.intersectionNumber_baseChange m.y false
    (q.p.ch false).EE (m.t.ch false).jE (m.t.ch false).jE_inj (m.t.ch false).jE_range
  have hXo : ∀ v, IsUnit (Xo v).det := h.elim fun _ h' v => (h'.2 v).2
  obtain ⟨s', -⟩ := exists_side hF m c Xo hXo (fun u => (w.D o.Z).plEq u) fun _ => ∅
  obtain ⟨s, ε, h1, h2, h3⟩ := exists_side hF m c Xo hXo (fun u => (w.D o.Z).plEq u)
    fun u => s'.p0.s.RRset ((w.D o.Z).what₂.muAt u)
  refine ⟨s, n, c, Xo, ε, h, h1, h2, fun x => (h3 x).trans (forall_congr' fun u => ?_)⟩
  rw [RRset_side s s']
  exact Iff.rfl

set_option maxHeartbeats 1000000 in
theorem read_of_good (hF : o.Fits) (m : Moved o) (s : Side0 o) (hs : Good m s) (Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0)
    (hIsh : ∀ x, HEq (Y.Ish.jE x).1 ((m.t.ch true).jE x)) (hIz : ∀ x, HEq (Y.Iz.jE x).1 ((m.t.ch false).jE x)) :
    Nonempty (RationalReadingWithoutCongruence m.z.R m.z.F s.p0 Y) :=
  hs.elim fun n hs => hs.elim fun c hs => hs.elim fun Xo hs => hs.elim fun ε0 hs => hF.div.1.elim fun ε hε =>
    reading_level_zero_of_side_data m.z.R m.z.F m.z.cG m.z.pins m.intersectionNumber_baseChange s.p0 Y m.y (m.t.ch true).jE q.p.nR q.p.cR q.p.Xo m.t.rr ε
      (fun x => (hIsh _).trans (heq_of_eq (congrArg (m.t.ch true).jE (hε.1 x)))) hε.2
      (m.t.ch false).jE n c Xo hs.1 ε0
      (fun x => (hIz _).trans (heq_of_eq (congrArg (m.t.ch false).jE (hs.2.1 x)))) hs.2.2.1
      (hF.div.2 o.S o.N o.G) hs.2.2.2

end GlobalTheory.Mem.R3.Rw.GoodSideLattices

namespace GlobalTheory.Mem.R3.Rw

set_option maxHeartbeats 1000000 in

theorem exists_side_reading_level_zero : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), Inputs (w.D o.Z) → o.Fits → ∀ m : Moved o, ∃ s : Side0 o, ∀ Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0, Y.tupT = m.y.tupT → (∀ x, HEq (Y.Ish.jE x).1 ((m.t.ch true).jE x)) → (∀ x, HEq (Y.Iz.jE x).1 ((m.t.ch false).jE x)) → (∀ i x, HEq (Y.mj.eW i x) (m.t.lf.eW i x)) → Nonempty (RationalReadingWithoutCongruence m.z.R m.z.F s.p0 Y) :=
  fun _ _ _ _ _ _ _ _ _ _ _ hF m =>
    (GoodSideLattices.exists_good hF m).imp fun s hs Y _ h1 h2 _ => GoodSideLattices.read_of_good hF m s hs Y h1 h2

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IotaProjectionAdjointBasisRowEigenvalue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.KapRec.Eigen

theorem exists_scaled_ext {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} {W H : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : (Fin n → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (k : (Fin n → K) →ₛₗ[σ] H) {c : ℝ}
    (hc : ∀ x y, ⟪k x, k y⟫_ℂ = (c : ℂ) * ⟪j x, j y⟫_ℂ) :
    ∃ u : W →ₗ[ℂ] H, (∀ w, ‖u w‖ ^ 2 = c * ‖w‖ ^ 2) ∧ ∀ x, u (j x) = k x := by
  let b : Module.Basis (Fin n) ℂ W := Module.Basis.mk hli (le_of_eq hsp.symm)
  let u := b.constr ℂ (fun i => k (Pi.single i 1))
  have hb : ∀ i, b i = j (Pi.single i 1) := fun i => Module.Basis.mk_apply _ _ _
  have hu : ∀ i, u (b i) = k (Pi.single i 1) := fun i => Module.Basis.constr_basis _ _ _ _
  have hdec : ∀ x : Fin n → K, x = ∑ i, x i • Pi.single i 1 := fun x => by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  have hj : ∀ x, j x = ∑ i, σ (x i) • b i := fun x => by
    conv_lhs => rw [hdec x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, hb]
  have hk : ∀ x, k x = ∑ i, σ (x i) • k (Pi.single i 1) := fun x => by
    conv_lhs => rw [hdec x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ]
  have hA : ∀ x, u (j x) = k x := fun x => by
    rw [hj, map_sum, hk]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hu]
  have hbas : ∀ i l, ⟪u (b i), u (b l)⟫_ℂ = (c : ℂ) * ⟪b i, b l⟫_ℂ := fun i l => by
    rw [hu, hu, hb, hb, hc]
  have key : ∀ z w, ⟪u z, u w⟫_ℂ = (c : ℂ) * ⟪z, w⟫_ℂ := fun z w => by
    rw [← b.sum_repr z, ← b.sum_repr w]
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hbas, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  refine ⟨u, fun w => ?_, hA⟩
  have h := key w w
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by push_cast; exact h)

set_option maxHeartbeats 2000000 in

theorem topMap_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∃ uA : D.what₂.Amb (Y.tup A3.A.μ0) →ₗ[ℂ] (R.HX A3.A.μ0).H, (∀ x, ‖uA x‖ ^ 2 = RealDat.nP F.lv2 true * ‖x‖ ^ 2) ∧ ∀ x, uA (Y.jA A3.A.μ0 x) = R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH
  have hFT := Y.formsA A3.A.μ0
  have hpos : (0 : ℝ) < RealDat.nP F.lv2 true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  let rf : (Fin (rDim D A3.A F.P1 F.ψ1 A3.A.μ0) → D.what₂.LL) →ₗ[D.what₂.LL] A3.A.fam.amb.FR A3.A.μ0 :=
    { toFun := rowForm A3.A F.P1 F.ψ1 A3.A.μ0
      map_add' := DatApi.rowForm_add A3.A F.P1 F.ψ1 A3.A.μ0
      map_smul' := DatApi.rowForm_smul A3.A F.P1 F.ψ1 A3.A.μ0 }
  refine exists_scaled_ext D.what₂.embLL (Y.jA A3.A.μ0) hFT.li hFT.span ((R.jX A3.A.μ0).comp rf) fun x y => ?_
  have h1 : (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * ⟪R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x), R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A3.A F.P1 F.ψ1 A3.A.μ0) x y) :=
    GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum D G Pl0 T A3.A Ks R.toRealDat F.lv2 hP.char.base true A3.A.μ0 x y
  have alg : ∀ a : ℂ, a = ((RealDat.nP F.lv2 true : ℝ) : ℂ) * ((((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * a) := fun a => by
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]
  rw [hFT.inner x y]
  refine Eq.trans ?_ (congrArg (fun z => ((RealDat.nP F.lv2 true : ℝ) : ℂ) * z) h1)
  exact alg ⟪R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x), R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 y)⟫_ℂ

theorem iiStar_apply_eq {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (μ : D.what₂.Tup) (y : EE) :
    (S.iotaQ μ ∘ₗ LinearMap.adjoint (S.iotaQ μ)) y = S.iota μ (S.eOp μ (LinearMap.adjoint (S.iota μ) y)) := by
  set w := LinearMap.adjoint (S.iotaQ μ) y with hw
  set z := LinearMap.adjoint (S.iota μ) y with hz
  have hQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), (w : S.Amb μ)⟫_ℂ = ⟪(q : S.Amb μ), z⟫_ℂ := by
    intro q
    rw [← Submodule.coe_inner, hw, hz, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
    rfl
  have heV : ∀ x ∈ S.V0 μ, S.eOp μ x = x := by
    rintro _ ⟨a, rfl⟩
    exact congrArg (fun f : S.Amb μ →ₗ[ℂ] S.Amb μ => f a) (S.eOp_idem μ)
  set d := S.eOp μ z - (w : S.Amb μ) with hd
  have hdV : d ∈ S.V0 μ := sub_mem (LinearMap.mem_range_self _ _) w.2.1
  have hdQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), d⟫_ℂ = 0 := by
    intro q
    rw [hd, inner_sub_right, hQ, ← S.eOp_sa μ, heV _ q.2.1, sub_self]
  have hdU : d ∈ S.Usp μ := by
    set r := d - (S.Usp μ).starProjection d with hr0
    have hUV : S.Usp μ ≤ S.V0 μ := inf_le_left
    have hr : r ∈ S.Qsp μ :=
      ⟨sub_mem hdV (hUV (Submodule.starProjection_apply_mem _ _)), Submodule.sub_starProjection_mem_orthogonal d⟩
    have h1 : ⟪r, d⟫_ℂ = 0 := hdQ ⟨r, hr⟩
    have h2 : ⟪r, (S.Usp μ).starProjection d⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hr.2
    have h3 : ⟪r, r⟫_ℂ = 0 := by
      conv_lhs => rw [hr0]
      rw [inner_sub_right, ← hr0, h1, h2, sub_zero]
    have h4 : r = 0 := inner_self_eq_zero.1 h3
    rw [hr0, sub_eq_zero] at h4
    rw [h4]
    exact Submodule.starProjection_apply_mem _ _
  have hk : S.iota μ d = 0 := hdU.2
  rw [hd, map_sub, sub_eq_zero] at hk
  exact hk.symm

theorem transport_eig {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) {μ μ' : D.what₂.Tup}
    (hμ : μ = μ') (uA : S.Amb μ →ₗ[ℂ] E) (uE : EE →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n) (nA : ∀ x, ‖uA x‖ ^ 2 = n * ‖x‖ ^ 2)
    (nE : ∀ y, ‖uE y‖ ^ 2 = n * ‖y‖ ^ 2) (hι : ∀ x, uE (S.iota μ x) = Θ (uA x)) (y : EE)
    (hy : LinearMap.adjoint Θ (uE y) ∈ (S.V0 μ).map uA) {a : ℂ} (ha : Θ (LinearMap.adjoint Θ (uE y)) = a • uE y) :
    S.iota μ' (S.eOp μ' (LinearMap.adjoint (S.iota μ') y)) = a • y := by
  subst hμ
  rw [← iiStar_apply_eq]
  exact GlobalTheory.KappaLevels.iota_adjoint_transport Θ (S.iota μ) (S.V0 μ) uA uE hn nA nE (fun x _ => hι x) y hy ha

set_option maxHeartbeats 4000000 in

theorem eigen : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, (RowSide.sharp D).iota D.what₂.mu0 ((RowSide.sharp D).eOp D.what₂.mu0 (LinearMap.adjoint ((RowSide.sharp D).iota D.what₂.mu0) (D.what₂.onb σ))) = ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) : ℝ) : ℂ) • D.what₂.onb σ := by
  intro hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hL hI σ
  obtain ⟨uE, -, nE, hE⟩ := GlobalTheory.Adopt.levelRowsReading_embedding_goodRowsModel_with_norm D G Pl0 T A3.A Ks R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop true D.what₂.EE
    (RowSide.sharp D) Y.Ish hP.char.base.models.HE Y.tied.sharp.ee
  obtain ⟨uA, nA, hA⟩ := topMap_exists D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  obtain ⟨p, hp, hl⟩ := GlobalTheory.T.basisRow_mem_definiteFamily_type_part hCRD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hI uE hE σ
  have hup := GlobalTheory.T.adjoint_compositeLift_row_mem_span_goodRationalForms hCRD.2.2.2.2 D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH uE hE (D.what₂.onb σ)
  have hdt := (GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector hCRD D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH).1 A3.A.μ0
  have ha : R.Th A3.A.μ0 (LinearMap.adjoint (R.Th A3.A.μ0) (uE (D.what₂.onb σ))) =
      ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) : ℝ) : ℂ) • uE (D.what₂.onb σ) := by
    refine (hH.prim.thmB A3.A.μ0 p (uE (D.what₂.onb σ)) hp).trans ?_
    rw [hl]
  have hpos : (0 : ℝ) < RealDat.nP F.lv2 true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have hFT := Y.formsA A3.A.μ0
  have hι : ∀ a, uE ((RowSide.sharp D).iota (Y.tup A3.A.μ0) a) = R.Th A3.A.μ0 (uA a) := by
    have key : uE ∘ₗ (RowSide.sharp D).iota (Y.tup A3.A.μ0) = R.Th A3.A.μ0 ∘ₗ uA := by
      refine LinearMap.ext_on_range hFT.span fun i => ?_
      show uE ((RowSide.sharp D).iota (Y.tup A3.A.μ0) (Y.jA A3.A.μ0 (Pi.single i 1))) =
        R.Th A3.A.μ0 (uA (Y.jA A3.A.μ0 (Pi.single i 1)))
      rw [← GlobalTheory.Mem.R3.DTheta.iota_sharp, hA]
      have h1 := hdt (Pi.single i 1)
      rw [hE] at h1
      exact hP.char.base.models.HE.1 (PiTensorProduct.lift.injective h1)
    exact fun a => LinearMap.congr_fun key a
  have hy : LinearMap.adjoint (R.Th A3.A.μ0) (uE (D.what₂.onb σ)) ∈
      ((RowSide.sharp D).V0 (Y.tup A3.A.μ0)).map uA := by
    refine (Submodule.span_le.2 ?_) hup
    rintro _ ⟨x, rfl⟩
    exact ⟨Y.jA A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x), ⟨Y.jA A3.A.μ0 x, hFT.op_eq x⟩, hA _⟩
  exact transport_eig (RowSide.sharp D) (R.Th A3.A.μ0) Y.tup0 uA uE hpos nA nE hι (D.what₂.onb σ) hy ha

end GlobalTheory.KapRec.Eigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NAllCWithLoc
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting.FitAll

theorem nAllC_withLoc : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL), LpCmp hL → CgCmp hL → ∀ (D' : D7) (b : NBuilt hL D') (fr : OmFrame b.D), fr.jE = b.jE → (PhtOn b.A.wd fr fun _ _ _ _ => True) → Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → lowPr b.D ⊆ b.low → ∃ a : NAllC (withLoc b.L) (chL b.L b.C), (⟨a.cf, a.tp⟩ : Σ c : CharFrame (withLoc b.L), TupTied (withLoc b.L) c (chL b.L b.C)) = ⟨cfL b.L b.cf, tpL b.L b.tp⟩ ∧ a.gal.fr.jE = b.jE ∧ a.gal.mt = mtL b.L b.M ∧ ExpRel b.L b.Bs.exp a.exp ∧ Nonempty (NCharTied (withLoc b.L) (cfL b.L b.cf) (chL b.L b.C) (tpL b.L b.tp)) ∧ NGalChrTied (withLoc b.L) (cfL b.L b.cf) (chL b.L b.C) (tpL b.L b.tp) ∧ ∀ F : RowFrame (withLoc b.L), F.rep = b.rep → RowLocTied (withLoc b.L) a.gal.lp F := by
  intro hL hLp hCg D' b fr hfr hpht hE hCh hlow
  obtain ⟨g, hgj, hgm, hgt, ⟨dat⟩, ⟨cov⟩, hrow⟩ :=
    GlobalTheory.FitGal.galTied_withLoc hL hLp D' b fr hfr hpht hE.star hE.int hE.split hCh
  obtain ⟨⟨nt⟩, ⟨lt⟩⟩ := GlobalTheory.HeightCounting.nTied_locTied_of_built hL hCg D' b
  obtain ⟨TO⟩ := GlobalTheory.HeightCounting.typesOpen_withLoc b.D b.cf b.jE b.A b.low b.Pq b.S b.hL b.eig b.θ b.Bs b.M b.C b.tp b.ch b.mt
    hE.star hE.int hE.split hCh b.big b.L b.Sp b.Au b.ss
  have rho : NR.NRhoTied (withLoc b.L) := GlobalTheory.HeightCounting.nRhoTied_withLoc hL D' b hE.star hE.int hE.split hCh TO
  obtain ⟨Tw, hX⟩ := GlobalTheory.T.exists_twisted_open_exponent hL D' b hE hCh
  have ty : NormalizedTypesCompatibility (withLoc b.L) b.jE :=
    { eM := TO.par.eM, eM_K := TO.par.eM_K, tA := TO.grp.tA, tκ := TO.grp.tκ, teichC_def := TO.grp.teichC_def,
      iota_loc := fun i => ⟨TO.plB _, TO.plκ _, TO.plB_loc i, TO.plB_iota i⟩,
      ζ := TO.grp.ζ, ζ_gen := TO.grp.ζ_gen, O := TO.grp.O, eSer_def := TO.grp.eSer_def, kv := TO.grp.kv,
      tg_tame := TO.grp.tg_tame, O_equiv := TO.grp.O_equiv, O_tw := TO.grp.O_tw, eP := TO.par.eP,
      locPar_def := TO.par.locPar_def }
  let F0 : TwFrame (withLoc b.L) := ⟨Tw.twF.K0, Tw.twF.eO0, Tw.twF.j0, Tw.twF.Lw, Tw.twF.eO, Tw.twF.eOk, Tw.twF.iCq, Tw.twF.S0x⟩
  have hlow' : lowPr (withLoc b.L) ⊆ b.low := hlow
  have tw : NTwTied (withLoc b.L) F0 := by
    have T := Tw.tw
    have hN : Ideal.absNorm (withLoc b.L).host.ccK ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (withLoc b.L).host.ccK_ne_bot
    have hd : (NumberField.discr (withLoc b.L).host.E).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero (withLoc b.L).host.E)
    exact ⟨T.pl_emb, T.ringSpec_baseIntegersEquiv_algebraMap, T.ringSpec_baseEmbedding_compatible, T.eO_alg, T.eOk_alg, T.mu_g, T.hk_split, T.ringSpec_excludedPlaces_eq, T.concreteTwistFrame_extraExcludedPlaces_conj, T.B_range,
      T.sig_inj, T.qs_pos,
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hlow' (by simp [lowPr, Nat.mem_primeFactors, hp, h, hN])),
      fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (hlow' (by simp [lowPr])), fun i => T.concreteTwistFrame_extraExcluded_over_smallPrimes i _ (hlow' (by simp [lowPr])),
      fun i p hp h => T.concreteTwistFrame_extraExcluded_over_smallPrimes i p (hlow' (by simp [lowPr, Nat.mem_primeFactors, hp, h, hd]))⟩
  refine ⟨
    { gal := g, n := (b.eq ▸ nt), loc := (b.eq ▸ lt), data := dat, cover := (hgm ▸ cov), chiD := Tw.chiD, chi := Tw.chi,
      rho := rho, types := (hgj.symm ▸ ty), twF := F0, tw := tw, nct := Tw.ch.nct, exp := Tw.exp, choice := Tw.ch.choice,
      eMt_level := by rw [hgm]; exact Tw.ch.eMt_level,
      cf := cfL b.L b.cf, tp := tpL b.L b.tp, tupLink := hgt,
      eta_eq := Tw.eta_eq, ringSpec_normalisedCharacter_eq := Tw.ringSpec_normalisedCharacter_eq, del_eq := Tw.del_eq, psi_eq := Tw.psi_eq,
      plB := TO.plB, plκ := TO.plκ, plB_loc := TO.plB_loc, plB_iota := TO.plB_iota,
      etaT_link := Tw.etaT_link, muC_link := Tw.muC_link, iCq_embO := Tw.iCq_embO, embO_star := Tw.embO_star },
    rfl, hgj, hgm, hX, ⟨Tw.chrN⟩, Tw.chrGal, hrow⟩

end GlobalTheory.HeightCounting.FitAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowBasisCongruenceLengthsOtherLaterStagesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m) (R : RealDat3 a.D A3 Ks) (F : Face3 a.D A3), letI := alg b iK; (∀ j v, etaOf (real3 b R) (face3 b F) j v = etaOf R F j ((by with_unfolding_all exact (v :)))) ∧ ∀ (y : Hd R.toRealDat) (y' : Hd (real3 b R).toRealDat) (bb : Bool) (E : Hs) jE jE' n c Xo, HEq jE' jE → RrT F y bb (E := E) jE n c Xo → RrT (face3 b F) y' bb (E := E) jE' n c ((by with_unfolding_all exact (Xo :))) := by
  first | exact @GlobalTheory.Mem.R3.Rw.rr_eta_tr | exact GlobalTheory.Mem.R3.Rw.rr_eta_tr | (intros; apply GlobalTheory.Mem.R3.Rw.rr_eta_tr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsFiniteGroupActionEqFlagLevelRightTranslaStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormsFiniteGroupAction_eq_flagLevelRightTranslation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      ∃ a : Bridge.ActTie (Bridge.ratF X.toD7.sp.X') P (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q (levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch ((famR X I hX U Xg tr).A.leftGroupActionRight t),
        ∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
          eG (a.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) := by
  first | exact @GlobalTheory.Mem.R3.RowAct.act_tie | exact GlobalTheory.Mem.R3.RowAct.act_tie | (intros; apply GlobalTheory.Mem.R3.RowAct.act_tie <;> assumption)
end

