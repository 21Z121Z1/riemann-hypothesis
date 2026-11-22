import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0377
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0387
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualCocyclesModPrimePowUnramifiedOutsideSBou
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0378
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0390
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0391

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ArchimedeanInvariantsCard
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.GwIneq.Arch

theorem isUnit_two (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (c : Coef l) (n : ℕ) : IsUnit (2 : Qn c n) := by
  have hodd : Odd (l ^ n) := ((Fact.out : l.Prime).odd_of_ne_two hl).pow
  obtain ⟨k, hk⟩ := hodd
  have h0 : ((l ^ n : ℕ) : Qn c n) = 0 := by
    have := kill c n (1 : Qn c n)
    rwa [nsmul_eq_mul, mul_one] at this
  have e : (2 : Qn c n) * ((k + 1 : ℕ) : Qn c n) = ((l ^ n : ℕ) : Qn c n) + 1 := by
    rw [hk]; push_cast; ring
  rw [h0, zero_add] at e
  exact isUnit_iff_exists_inv.mpr ⟨_, e⟩

theorem trace_eq_zero {R : Type} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R) (hXX : X * X = 1)
    (hdet : X.det = -1) : X.trace = 0 := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two]
  have e00 := congrFun (congrFun hXX 0) 0
  have e10 := congrFun (congrFun hXX 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  linear_combination (X 0 0 - (X 0 0 + X 1 1)) * e00 + X 0 0 * hdet + X 0 1 * e10

theorem card_fixed_cc (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) (c : Coef l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) (n : ℕ) (w : InfinitePlace ℚ) (s : G ℚ Ω) (hs : IsCCAt w s) :
    Nat.card {v : Mn c n // matQ c n W hint s *ᵥ v = v} = Nat.card (Qn c n) := by
  obtain ⟨j, hj, -⟩ := hs
  have hss : s * s = 1 := by
    ext x
    apply j.injective
    show j (s (s x)) = j x
    rw [hj, hj]; simp
  have hXX : matQ c n W hint s * matQ c n W hint s = 1 := by
    rw [← matQ_mul, hss, matQ_one]
  have hd : (mat W s).det = -1 := by
    have h := hW.odd s ⟨j, hj⟩
    have h2 : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
      simp [dt, mat, Matrix.GeneralLinearGroup.val_det_apply]
    rw [← h2, h]; simp
  have hdet : (matQ c n W hint s).det = -1 := by
    rw [Matrix.det_fin_two] at hd ⊢
    simp only [matQ_apply]
    rw [← map_mul, ← map_mul, ← map_sub, ← map_one (red c n), ← map_neg]
    congr 1
    apply Subtype.ext
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_one]
    exact hd
  exact GlobalTheory.OddInvolution.card_fixed l (Qn c n) _ (isUnit_two l hW.l_odd c n) hXX hdet
    (trace_eq_zero _ hXX hdet)

theorem archimedean_h0_card_eq : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ cc : InfinitePlace ℚ → G ℚ Ω, (∀ w, w.IsReal → IsCCAt w (cc w)) → archH0Card S (rhoS c n W hint S hN) cc = Nat.card (Qn c n) := by
  intro l _ Ω _ _ _ e S A W hW c hint hN n _ cc hcc
  classical
  unfold archH0Card
  have hfil : (Finset.univ.filter (fun w : InfinitePlace ℚ => w.IsReal)) = {Rat.infinitePlace} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun h => h ▸ Rat.isReal_infinitePlace⟩
  rw [IsTotallyReal.nrComplexPlaces_eq_zero ℚ, pow_zero, mul_one]
  convert Finset.prod_singleton (fun w : InfinitePlace ℚ =>
    Nat.card {m : Mn c n // rhoS c n W hint S hN (toGS Ω _ (cc w)) m = m}) Rat.infinitePlace using 1
  · rw [hfil]
  · exact (card_fixed_cc l Ω e S A W hW c hint n _ _ (hcc _ Rat.isReal_infinitePlace)).symm

end GlobalTheory.Ord2.GwIneq.Arch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BlochKatoCocycleUnramifiedAndGreenbergOrdinaryStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_cocycle_unramified_and_greenbergOrdinary : Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → Unr W z ∧ Gr W A z := by
  first | exact @GlobalTheory.Ord2.bk_unr_gr | exact GlobalTheory.Ord2.bk_unr_gr | (intros; apply GlobalTheory.Ord2.bk_unr_gr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualCocyclesModPrimePowUnramifiedOutsideSBouStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded_alt : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ n : ℕ, ∃ B : ℕ, ∀ (N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, Coc1 c n (dual1 W) ⊤ (z i) ∧ ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z i a) 0) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → N ≤ B := by
  first | exact @GlobalTheory.Ord2.GwFin.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded | exact GlobalTheory.Ord2.GwFin.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded | (intros; apply GlobalTheory.Ord2.GwFin.card_dualCocyclesModPrimePow_unramifiedOutsideS_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardOrdinaryLocalConditionModPrimePowLeConstMul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwIneq.CardOrd

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem span_eq_Ik (c : Coef l) (n : ℕ) : Ideal.span {((l : ℕ) : c.O) ^ n} = Ik c n := by
  ext x
  rw [Ideal.mem_span_singleton, mem_Ik]
  exact (GlobalTheory.Coef.norm_le_norm_pow_iff_dvd l c n x).symm

def levEquiv (c : Coef l) (n : ℕ) : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n) ≃+ Qn c n :=
  (Ideal.quotEquivOfEq (span_eq_Ik c n)).toAddEquiv

theorem levEquiv_mk (c : Coef l) (n : ℕ) (x : c.O) :
    levEquiv c n (UpperTheory.V.X.Lev.mk (((l : ℕ) : c.O) ^ n) x) = red c n x := rfl

theorem card_lev (c : Coef l) (n : ℕ) :
    Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) = Nat.card (Qn c n) :=
  Nat.card_congr (levEquiv c n).toEquiv

theorem levEquiv_smul (c : Coef l) (n : ℕ) (a : c.O) (x : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) :
    levEquiv c n (a • x) = red c n a * levEquiv c n x := by
  obtain ⟨y, rfl⟩ := UpperTheory.V.X.Lev.mk_surjective _ x
  rw [← map_smul, smul_eq_mul, levEquiv_mk, levEquiv_mk, map_mul]

def lineInc (c : Coef l) (n : ℕ) : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n) →+ Mn c n :=
  (AddMonoidHom.single (fun _ : Fin 2 => Qn c n) 0).comp (levEquiv c n).toAddMonoidHom

theorem lineInc_apply (c : Coef l) (n : ℕ) (x : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) :
    lineInc c n x = Pi.single 0 (levEquiv c n x) := rfl

theorem lineInc_injective (c : Coef l) (n : ℕ) : Function.Injective (lineInc c n) :=
  fun x y h => (levEquiv c n).injective (by
    have h0 := congrFun h 0
    simpa [lineInc_apply] using h0)

variable [IsAlgClosure ℚ Ω]

theorem lineInc_equiv (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (B : ValuationSubring Ω)
    (hup : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (θ : Dec (F := ℚ) B →* c.Oˣ)
    (hθ : ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = mat W g 0 0) (g : Dec (F := ℚ) B)
    (x : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) :
    lineInc c n (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ g x) =
      ((rhoS c n W hint S hN).comp (locHom (S : Set Pl) B)) g (lineInc c n x) := by
  have h1 : (θ g : c.O) = ⟨mat W g 0 0, hint g 0 0⟩ := Subtype.ext (hθ g)
  have h2 : matQ c n W hint g 1 0 = 0 := by
    rw [matQ_apply]
    have : (⟨mat W g 1 0, hint g 1 0⟩ : c.O) = 0 := Subtype.ext (hup g g.2)
    rw [this, map_zero]
  show lineInc c n (((θ g : c.Oˣ) : c.O) • x) = matQ c n W hint g *ᵥ lineInc c n x
  rw [lineInc_apply, lineInc_apply, levEquiv_smul, h1]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, matQ_apply]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h2]

theorem card_ordCond_le (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (hcont : Continuous W) (B : ValuationSubring Ω)
    (hup : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (θ : Dec (F := ℚ) B →* c.Oˣ)
    (hθ : ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = mat W g 0 0)
    [Finite (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ))] :
    Nat.card (ordCond c n W hint S hN B) ≤
      Nat.card (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) := by
  set τ := Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ with hτ
  set σ := (rhoS c n W hint S hN).comp (locHom (S : Set Pl) B) with hσ
  have hσa : ∀ (g : Dec (F := ℚ) B) (y : Mn c n), σ g y = matQ c n W hint g *ᵥ y := fun _ _ => rfl
  have heq := lineInc_equiv c n W hint S hN B hup θ hθ
  set Φ := UpperTheory.V.X.h1MapOfAdditive τ σ (lineInc c n) heq with hΦ
  have hsub : (ordCond c n W hint S hN B : Set (H1 σ)) ⊆ Set.range Φ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨x, hx⟩ := (mem_ordZ _).1 (Submodule.mem_comap.1 hz)

    set m : Mn c n := Pi.single 1 x with hm
    have hbc : Continuous fun g : Dec (F := ℚ) B => σ g m - m := by
      have hc : ∀ i j, Continuous fun g : Dec (F := ℚ) B => matQ c n W hint g i j := fun i j =>
        (continuous_matQ_apply c n W hint hcont i j).comp continuous_subtype_val
      refine continuous_pi fun i => ?_
      simp only [hσa, Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact (((hc i 0).mul continuous_const).add ((hc i 1).mul continuous_const)).sub continuous_const
    let bZ : Z1 σ := ⟨fun g => σ g m - m, hbc, fun g h => by
      simp only [map_mul, Module.End.mul_apply, map_sub]
      abel⟩
    have hbB : bZ ∈ (B1 σ).comap (Z1 σ).subtype := (mem_coboundaries1 σ _).2 ⟨m, fun g => rfl⟩
    set zb : Z1 σ := z - bZ with hzb
    have hzb1 : ∀ g, zb.1 g 1 = 0 := by
      intro g
      show z.1 g 1 - (σ g m - m) 1 = 0
      have hx' : z.1 g 1 = matQ c n W hint g 1 1 * x - x := hx g
      rw [hσa, hx']
      have hm0 : m 0 = 0 := rfl
      have hm1 : m 1 = x := rfl
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hm0, hm1]
      ring
    have hzbι : ∀ g, zb.1 g = lineInc c n ((levEquiv c n).symm (zb.1 g 0)) := by
      intro g
      rw [lineInc_apply, AddEquiv.apply_symm_apply]
      ext i
      fin_cases i
      · simp
      · simp [hzb1 g]
    let w : Dec (F := ℚ) B → UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n) := fun g => (levEquiv c n).symm (zb.1 g 0)
    have hw : w ∈ Z1 τ := by
      refine ⟨(continuous_of_discreteTopology (f := fun y : Mn c n => (levEquiv c n).symm (y 0))).comp zb.2.1,
        fun g h => lineInc_injective c n ?_⟩
      rw [map_add, heq, ← hzbι, ← hzbι, ← hzbι]
      exact zb.2.2 g h
    refine ⟨Submodule.Quotient.mk ⟨w, hw⟩, ?_⟩
    rw [hΦ, UpperTheory.V.X.h1MapOfAdditive_mk]
    have e1 : UpperTheory.V.X.cocycleMapOfEquivariant τ σ (lineInc c n) heq ⟨w, hw⟩ = zb :=
      Subtype.ext (funext fun g => (hzbι g).symm)
    rw [e1, hzb, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 hbB, sub_zero]
    rfl
  calc Nat.card (ordCond c n W hint S hN B) = Nat.card (ordCond c n W hint S hN B : Set (H1 σ)) := rfl
    _ ≤ Nat.card (Set.range Φ) := Nat.card_mono (Set.finite_range Φ) hsub
    _ ≤ Nat.card (H1 τ) := Finite.card_range_le Φ

end GlobalTheory.Ord2.GwIneq.CardOrd

namespace GlobalTheory.Ord2.GwIneq.CardOrd

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_theta (c : Coef l) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hcont : Continuous W)
    (hdet : dt W ^ 2 = 1) (B : ValuationSubring Ω) (hup : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) :
    ∃ θ : Dec (F := ℚ) B →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧
      ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = mat W g 0 0 := by
  have hm : Continuous fun s => mat W s := Units.continuous_val.comp hcont
  refine GlobalTheory.LocChar.unit_of_integral l Ω c B (fun s => mat W s 0 0)
    (fun s => eps l s * (mat W s 1 1 * (mat W s).det)) ((hm.matrix_elem 0 0).continuousOn) ?_ ?_
  · intro s hs
    have hdetO : (mat W s).det ∈ c.O := by
      rw [Matrix.det_fin_two]
      exact c.O.sub_mem (c.O.mul_mem (hint s 0 0) (hint s 1 1)) (c.O.mul_mem (hint s 0 1) (hint s 1 0))
    refine ⟨hint s 0 0, c.O.mul_mem (CupCob.eps_mem c s) (c.O.mul_mem (hint s 1 1) hdetO), ?_⟩
    have hd : (mat W s).det = mat W s 0 0 * mat W s 1 1 := by
      rw [Matrix.det_fin_two, hup s hs, mul_zero, sub_zero]
    have h2 := CupCob.det_sq W hdet s
    calc mat W s 0 0 * (eps l s * (mat W s 1 1 * (mat W s).det))
        = eps l s * ((mat W s 0 0 * mat W s 1 1) * (mat W s).det) := by ring
      _ = eps l s * (mat W s).det ^ 2 := by rw [← hd]; ring
      _ = eps l s := by rw [h2, mul_one]
  · intro s _ t ht
    show mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0
    simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have := hup t ht
    simp only [mat] at this
    rw [this, mul_zero, add_zero]

variable [IsAlgClosure ℚ Ω]

theorem exists_ne_one (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) :
    ∃ s ∈ Dec (F := ℚ) A, mat W s 0 0 ≠ 1 := by
  set D := Dec (F := ℚ) A with hDdef
  have hup : ∀ s ∈ D, mat W s 1 0 = 0 := hW.upper
  have h00 : ∀ s t, t ∈ D → mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0 := by
    intro s t ht
    simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have := hup t ht
    simp only [mat] at this
    rw [this, mul_zero, add_zero]
  have hv : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hA, hlv⟩ := hW.atL
    simpa using (hA _).2 hlv
  obtain ⟨u0, hu0⟩ := GrOfKill.exists_unit_one_add l
  obtain ⟨t, htI, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u0
  have heps : eps l t = ((1 + l : ℕ) : Qbar l) := by
    simp [eps, cycBar, htu, hu0]
  obtain ⟨m, hm1, hm⟩ := hW.wt
  have htD : t ∈ D := Ine_le_Dec A htI
  have hpow00 : ∀ s ∈ D, ∀ k : ℕ, mat W (s ^ k) 0 0 = mat W s 0 0 ^ k := by
    intro s hs k
    induction k with
    | zero => simp [mat]
    | succ k ih => rw [pow_succ, h00 _ _ hs, ih, pow_succ]
  refine ⟨t ^ m, D.pow_mem htD m, fun h => ?_⟩
  have hT : mat W (t ^ m) 0 0 = (((1 + l) ^ (e * m) : ℕ) : Qbar l) := by
    rw [hpow00 t htD, hm t htI, heps]; push_cast; ring
  rw [hT] at h
  have h1 : (1 + l) ^ (e * m) = 1 := by exact_mod_cast h
  have hl1 : 1 < 1 + l := by have := (Fact.out : l.Prime).two_le; omega
  have : 1 < (1 + l) ^ (e * m) :=
    Nat.one_lt_pow (Nat.mul_ne_zero (by have := hW.e_pos; omega) (by omega)) hl1
  omega

theorem card_ord : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W →
    ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1),
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ v : S, IsPlaceOver A v.1 →
      Nat.card (Lc c n W hint S hN A v) ≤ C * Nat.card (Qn c n) := by
  intro hL l _ Ω _ _ _ e S A W hW c hint hN
  obtain ⟨θ, hθc, hθ⟩ := exists_theta c W hint hW.cont hW.det2 A hW.upper
  have h1 : ∃ g, θ g ≠ 1 := by
    obtain ⟨s, hs, hne⟩ := exists_ne_one e S A W hW
    refine ⟨⟨s, hs⟩, fun h => hne ?_⟩
    have := hθ ⟨s, hs⟩
    rw [h] at this
    exact this.symm
  have h2 : ∃ g, θ g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g := by
    obtain ⟨s, hs, hne⟩ := hW.ne
    refine ⟨⟨s, hs⟩, fun h => hne ?_⟩
    have := hθ ⟨s, hs⟩
    rw [h] at this
    exact this.symm
  obtain ⟨C, hC⟩ := GlobalTheory.LocChar.local_character_h1_bound hL.lf hL.lt hL.le l Ω c A hW.atL θ hθc h1 h2
  refine ⟨C, fun n hn v hv => ?_⟩
  obtain ⟨hfin, hcard⟩ := hC n hn
  have hAv : Av A S v = A := if_pos hv
  have hLc : Nat.card (Lc c n W hint S hN A v) = Nat.card (ordCond c n W hint S hN (Av A S v)) :=
    congrArg (fun p : Submodule _ _ => Nat.card p)
      (if_pos hv : Lc c n W hint S hN A v = ordCond c n W hint S hN (Av A S v))
  rw [hLc, hAv, ← card_lev]
  exact (card_ordCond_le c n W hint S hN hW.cont A hW.upper θ hθ).trans hcard

end GlobalTheory.Ord2.GwIneq.CardOrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPrimePowTorsionSelmerClassesModPrimePowBoundStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_primePowTorsion_selmerClassesModPrimePow_bounded : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ n : ℕ, ∃ B : ℕ, ∀ (N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, Coc1 c n (dual1 W) ⊤ (z i) ∧ ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z i a) 0) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → N ≤ B) → ∀ m : ℕ, ∃ B : ℕ, ∀ (n N : ℕ) (z : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) → (∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j)) → (∀ i, Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z i s)) → N ≤ B := by
  first | exact @GlobalTheory.Ord2.TorsBound.tors_bound | exact GlobalTheory.Ord2.TorsBound.tors_bound | (intros; apply GlobalTheory.Ord2.TorsBound.tors_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousResiduePlaneGaloisRepUnramifiedOutside
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem resRep_contAction : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ContAction (resRep c W hO S hN) := by
  intro l _ Ω _ _ S W c hO hN hW

  have hred : ∀ m : ResPlane c, Continuous fun s : G ℚ Ω => resAct c W hO s m := by
    intro m
    rw [continuous_iff_continuousAt]
    intro s
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [locConst_mod_pow l Ω c W hW hO 1 s] with t ht
    have hw : wRed c W t = wRed c W s := by
      ext i j
      obtain ⟨o, ho, e⟩ := ht i j
      have hd : mat W t i j - mat W s i j ∈ c.O := c.O.sub_mem (hO t i j) (hO s i j)
      have h0 : redL c (mat W t i j - mat W s i j) = 0 :=
        (redL_eq_zero_iff c hd).2 ⟨o, ho, by rw [e, pow_one]⟩
      rw [redL_sub c (hO t i j) (hO s i j)] at h0
      exact sub_eq_zero.1 h0
    rw [resAct_apply, resAct_apply, hw]
  have hq : ∀ m : ResPlane c, Continuous fun g : GS Ω (S : Set Pl) => resRep c W hO S hN g m := by
    intro m
    rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
    exact hred m
  show Continuous fun p : GS Ω (S : Set Pl) × ResPlane c => (resRep c W hO S hN p.1) p.2
  exact continuous_prod_of_discrete_right.2 hq

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondCommutesHeckeU
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.KZ.DiamU

theorem isDiam_sgD_of_coprime' {N l d : ℕ} (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 : d = 1 := (Nat.coprime_zero_right d).1 hd
    subst h1
    exact Classical.epsilon_spec (p := IsDiam 0 l 1) ⟨1, Subgroup.one_mem _, by simp [en]⟩
  · exact Betti.isDiam_sgD hN.ne' hl hd

theorem upper_mul_eq {N l d : ℕ} {σ : SL(2, ℤ)} (hσ : IsDiam N l d σ) (hl : 0 < l) (j k : ℕ)
    (hk : (k : ZMod l) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod l) =
      (((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod l)) :
    ∃ s : SL(2, ℤ), IsDiam N l d s ∧
      !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) =
        (s : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (k : ℤ); 0, (l : ℤ)] := by
  obtain ⟨h0, hd⟩ := hσ
  rw [Subgroup.mem_inf] at h0
  have hcN := CongruenceSubgroup.Gamma0_mem.1 h0.1
  have hcl := CongruenceSubgroup.Gamma0_mem.1 h0.2
  have hdet := σ.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp only [en] at hd
  have hdiv : (l : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      k * ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + j * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hk hcl ⊢
    rw [hcl]
    linear_combination -hk
  obtain ⟨q, hq⟩ := hdiv
  set a := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b := (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set c := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set e := (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  set S : Matrix (Fin 2) (Fin 2) ℤ := !![a + j * c, q; l * c, e - c * k] with hSdef
  have hM : !![1, (j : ℤ); 0, (l : ℤ)] * (σ : Matrix (Fin 2) (Fin 2) ℤ) = S * !![1, (k : ℤ); 0, (l : ℤ)] := by
    ext i i'
    fin_cases i <;> fin_cases i' <;>
      simp [hSdef, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, e] <;> first | ring1 | linear_combination hq
  have hS : S.det = 1 := by
    have h := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, σ.det_coe] at h
    simp only [Matrix.det_fin_two_of] at h
    have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
    have : ((l : ℤ)) * 1 = S.det * (l : ℤ) := by linarith
    exact (mul_right_cancel₀ hl' (by linarith : S.det * (l : ℤ) = 1 * (l : ℤ)))
  refine ⟨⟨S, hS⟩, ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩, hM⟩
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod N) = 0
    rw [Int.cast_mul, hcN, mul_zero]
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    show ((l * c : ℤ) : ZMod l) = 0
    rw [Int.cast_mul, hcl, mul_zero]
  · simp only [en]
    simp [hSdef]
    rw [hcN]; simpa using hd

private def res (l : ℕ) (x : ℤ) : ℕ := (x % (l : ℤ)).toNat

private theorem res_lt {l : ℕ} (hl : 0 < l) (x : ℤ) : res l x < l := by
  have h1 := Int.emod_lt_of_pos x (show (0 : ℤ) < l by exact_mod_cast hl)
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  unfold res; omega

private theorem res_cast {l : ℕ} (hl : 0 < l) (x : ℤ) : ((res l x : ℕ) : ZMod l) = (x : ZMod l) := by
  have h2 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by exact_mod_cast hl.ne')
  rw [← Int.cast_natCast, res, Int.toNat_of_nonneg h2, ZMod.intCast_mod]

private theorem res_eq {l : ℕ} (hl : 0 < l) {x : ℤ} {j : ℕ} (hj : j < l) (h : (x : ZMod l) = j) : res l x = j := by
  rw [← res_cast hl, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (res_lt hl x)] at h
  exact h

theorem act_sgD_heckeU : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    (w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w →
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b) =
      X.heckeU l (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  intro Ω _ _ ε X N l _ w d hd _ b hb
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hσ := isDiam_sgD_of_coprime' hl.ne' hd
  have hcl := CongruenceSubgroup.Gamma0_mem.1 (Subgroup.mem_inf.1 hσ.1).2
  have hdet := (sgD N l d).det_coe
  rw [Matrix.det_fin_two] at hdet
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have hm : ∀ j : ℕ, 0 < (!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := fun j => by
    rw [Matrix.det_fin_two_of]; simpa using hl
  have key := fun j k => upper_mul_eq hσ hl j k
  generalize hA : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = A at hdet key
  generalize hB : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = B at hdet key
  generalize hE : (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = E at hdet key
  have hae : (A : ZMod l) * E = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at h
    rw [hcl] at h
    linear_combination h
  simp only [Tower.heckeU, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_nbij' (fun j : ℕ => res l ((B + j * E) * E)) (fun k : ℕ => res l ((k * A - B) * A))
    (fun j _ => Finset.mem_range.2 (res_lt hl _)) (fun k _ => Finset.mem_range.2 (res_lt hl _)) ?_ ?_ ?_
  · intro j hj
    refine res_eq hl (Finset.mem_range.1 hj) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((j : ZMod l) + (B + j * E) * A) * hae
  · intro k hk
    refine res_eq hl (Finset.mem_range.1 hk) ?_
    push_cast
    rw [res_cast hl]
    push_cast
    linear_combination ((k : ZMod l) + (k * A - B) * E) * hae
  · intro j _
    obtain ⟨s, hs, hM⟩ := key j (res l ((B + j * E) * E)) (by
      rw [res_cast hl]
      push_cast
      linear_combination ((B : ZMod l) + j * E) * hae)
    rw [Tower.act_act Ω ε X l _ _ (hm j) (hpos _), hM, ← Tower.act_act Ω ε X l _ _ (hpos _) (hm _),
      X.act_isDiam_eq hb hs]

end GlobalTheory.KZ.DiamU
end
end

