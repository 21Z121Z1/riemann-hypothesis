import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimInvFunHostFixingAutInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0692
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0697
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0708
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellOfQuotientCellRadicalPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeDefiniteUnitary
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem conclusion1_thirdSt : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SphericalInertData.Conclusion1 D' := by
  intro hL hP
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ _ => ?_⟩
  let T' : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { l.a.A.wdT with }
  let A' : AUSide (withLoc L) := { l.a.A.au with }
  have cg : CGTrue hL (withLoc L) T' := { l.a.cg with }
  have au : AUTrue hL (withLoc L) T' A' := fun j h1 h2 π s σ h => l.a.au j h1 h2 π s σ h
  exact GlobalTheory.T.base_change_of_hypotheses hP.bc hP.what₂.bern hP.ds hP.gen hP.std hL (withLoc L) T' A' cg au

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelCharacterEqProdSuperdiagonalSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.ThetaSt

section Gen

variable {D : D7}

theorem res_xiBar (kv : Σ k : Fin 2, D.nd.PlG k) {PP : Pl D.host.E} (e : PP = D.naut.plGw kv.1 kv.2)
    (res : kP PP ≃+* ZMod (D.host.g kv.1)) : res (xiBar D PP) = NX.xiRed D kv := by
  subst e
  obtain ⟨a, c, hc, hac, hmem⟩ := Formalism.IndefR.NX.xiRed_isXiRes D kv
  have h1 := Formalism.L2.Col.reduction_spec (D.naut.plGw kv.1 kv.2) (a := D.host.xi0) (r := a) (s := c) hc (by
    change (c : D.host.E) * D.host.xi0 = (a : D.host.E)
    rw [hac, mul_comm])
  have h2 : Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal (((NX.xiRed D kv).val : ℕ) : 𝓞 D.host.E) *
      Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal c = Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal a := by
    rw [← map_mul, Ideal.Quotient.eq]
    exact hmem
  have hc0 : Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal c ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h3 : Formalism.L2.Col.redP (D.naut.plGw kv.1 kv.2) D.host.xi0 =
      Ideal.Quotient.mk (D.naut.plGw kv.1 kv.2).asIdeal (((NX.xiRed D kv).val : ℕ) : 𝓞 D.host.E) := by
    apply mul_left_cancel₀ hc0
    rw [h1, ← h2, mul_comm]
  show res (Formalism.L2.Col.redP _ D.host.xi0) = _
  rw [h3, map_natCast, map_natCast, ZMod.natCast_zmod_val]

theorem baseLevelCharacter_eq_prod_superdiagonalSum {Pg : Finset (Pl D.host.E)} {r : ℕ} (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL)
    (y : (Formalism.L2.DIV.P0 Pg r ψ).H) :
    (((Formalism.L2.DIV.P0 Pg r ψ).chi y : D.what₂.LLˣ) : D.what₂.LL) =
      ∏ PP : ↥Pg, ψ PP.1 (edgeSum supEdge ((y : G0 Pg r) PP)) := by
  simp only [Formalism.L2.DIV.P0, LevelP.ofLocal]
  erw [MonoidHom.finset_prod_apply, Units.coe_prod]
  rfl

theorem supSum_map {κ : Type} [CommRing κ] {n : ℕ} (e : κ →+* ZMod n) {r : ℕ} (g : GL (Fin r) κ) :
    Formalism.L2.NX.supSum r ((Matrix.GeneralLinearGroup.map e g : GL (Fin r) (ZMod n)) : Matrix (Fin r) (Fin r) (ZMod n)) =
      e (edgeSum supEdge g) := by
  unfold Formalism.L2.NX.supSum edgeSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : (b : ℕ) = a + 1
  · have h' : supEdge a b := h
    rw [if_pos h, if_pos h']
    rfl
  · have h' : ¬ supEdge a b := h
    rw [if_neg h, if_neg h', map_zero]

def thOf (ζ : Fin 2 → ↥D.LL0) (hp : ∀ k, ζ k ^ D.host.g k = 1) (k : Fin 2) :
    Multiplicative (ZMod (D.host.g k)) →* (↥D.LL0)ˣ :=
  ((AddChar.zmodChar (D.host.g k) (hp k)).toMonoidHom.toHomUnits)⁻¹

theorem thOf_val (ζ : Fin 2 → ↥D.LL0) (hp : ∀ k, ζ k ^ D.host.g k = 1) (k : Fin 2) (z : ZMod (D.host.g k)) :
    (((thOf ζ hp k (Multiplicative.ofAdd z) : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) = ((ζ k : D.what₂.LL) ^ z.val)⁻¹ := by
  simp [thOf, MonoidHom.inv_apply, AddChar.toMonoidHom_apply, AddChar.zmodChar_apply]

theorem pow_of_emb (ζ : Fin 2 → ↥D.LL0)
    (hζ : ∀ k, D.what₂.embLL (ζ k : D.what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / (D.host.g k : ℂ))) (k : Fin 2) :
    ζ k ^ D.host.g k = 1 := by
  have hg : (D.host.g k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
  apply Subtype.ext
  apply D.what₂.embLL.injective
  have e1 : ((ζ k ^ D.host.g k : ↥D.LL0) : D.what₂.LL) = (ζ k : D.what₂.LL) ^ D.host.g k := rfl
  rw [e1, map_pow, hζ, ← Complex.exp_nat_mul]
  have e2 : ((D.host.g k : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (D.host.g k : ℂ)) = 2 * Real.pi * Complex.I := by
    field_simp
  rw [e2, Complex.exp_two_pi_mul_I]
  simp

theorem exists_theta {G : Type} [Group G] {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ}
    {eG : G ≃* G0g D.nd} (h : PsiPPTie D P0 ψ0 Ps ψs eG) (ζ : Fin 2 → ↥D.LL0)
    (hζ : ∀ k, D.what₂.embLL (ζ k : D.what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / (D.host.g k : ℂ))) :
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ, (∀ kk, θ kk ≠ 1) ∧
      (∀ g : G, g ∈ P0 ↔ eG g ∈ Formalism.IndefR.NX.U D.nd) ∧
      ∀ (u : P0) (hu : eG u ∈ Formalism.IndefR.NX.U D.nd),
        (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) =
          (((ψ0 u)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) := by
  have hp := pow_of_emb ζ hζ
  obtain ⟨Pg, pl, res, ψ, eC, hT, hW⟩ := h
  refine ⟨thOf ζ hp, fun k hk => ?_, fun g => ?_, fun u hu => ?_⟩
  ·
    have hg1 : 1 < D.host.g k := (D.host.g_prime k).one_lt
    have : Fact (1 < D.host.g k) := ⟨hg1⟩
    have e := congrArg (fun f : Multiplicative (ZMod (D.host.g k)) →* (↥D.LL0)ˣ =>
      (((f (Multiplicative.ofAdd 1) : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) hk
    simp only [thOf_val, ZMod.val_one, pow_one, MonoidHom.one_apply, Units.val_one] at e
    have e' : (ζ k : D.what₂.LL) = 1 := by
      have := congrArg (·⁻¹) e
      simpa using this
    have e2 := congrArg D.what₂.embLL e'
    rw [hζ, map_one] at e2
    exact ((Complex.isPrimitiveRoot_exp (D.host.g k) (D.host.g_prime k).ne_zero).ne_one hg1) e2
  ·
    rw [hT.p0, mem_U]
    change (∀ PP ∈ Set.univ, eC g PP ∈ unip _ _) ↔ _
    simp only [Set.mem_univ, forall_true_left]
    rw [pl.surjective.forall]
    refine forall_congr' fun kv => ?_
    rw [hT.comp g kv]
    have e : ∀ a b : Fin D.R.r, (Matrix.GeneralLinearGroup.map (res kv).toRingHom (eC g (pl kv))).val a b =
        res kv ((eC g (pl kv)).val a b) := fun _ _ => rfl
    simp only [e, EmbeddingLike.map_eq_zero_iff, EmbeddingLike.map_eq_one_iff]
    exact ⟨fun h => ⟨fun a b hab => h.1 hab, h.2⟩, fun h => ⟨fun a b hab => h.1 a b hab, h.2⟩⟩
  ·
    have hu0 : eC u ∈ (Formalism.L2.DIV.P0 Pg D.R.r ψ).H := (hT.p0 u).1 u.2
    rw [hT.chi0 u hu0, Units.val_inv_eq_inv_val, baseLevelCharacter_eq_prod_superdiagonalSum]
    have hfac : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv))) =
        (ζ kv.1 : D.what₂.LL) ^ (NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val := by
      intro kv
      have hres : res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv))) = NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
        rw [map_mul, res_xiBar kv (hT.place kv), hT.comp u kv, supSum_map]
        rfl
      rw [← hres]
      have hb : xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)) =
          (((res kv (xiBar D (pl kv).1 * edgeSum supEdge (eC u (pl kv)))).val : ℤ) : kP (pl kv).1) := by
        apply (res kv).injective
        rw [map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
      apply D.what₂.embLL.injective
      rw [hW kv _ _ hb, map_pow, hζ, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have lhs : (((psiUOf D.nd (NX.xiRed D) (thOf ζ hp) ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) =
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((ζ kv.1 : D.what₂.LL) ^ (NX.xiRed D kv * Formalism.L2.NX.supSum D.R.r
          (((eG u : G0g D.nd) kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).val)⁻¹ := by
      rw [psiUOf_apply, Units.coe_prod, IntermediateField.coe_prod]
      exact Finset.prod_congr rfl fun kv _ => thOf_val ζ hp kv.1 _
    rw [lhs, ← Fintype.prod_equiv pl (fun kv => ψ (pl kv).1 (edgeSum supEdge (eC u (pl kv)))) _ (fun _ => rfl),
      Finset.prod_inv_distrib]
    exact congrArg _ (Finset.prod_congr rfl fun kv _ => (hfac kv).symm)

end Gen

section State

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem roots_g (x : St P) (k : Fin 2) : ∃ ζ : ↥(Dof x).LL0,
    (Dof x).what₂.embLL (ζ : (Dof x).what₂.LL) = Complex.exp (2 * Real.pi * Complex.I / ((Dof x).host.g k : ℂ)) := by
  have hmem : (w.st x.o.Z).B.host.g k * ((w.st x.o.Z).B.host.g k - 1) ∈ [(w.st x.o.Z).B.restRowsFiniteGroupCard,
      (w.st x.o.Z).B.host.g 0 * ((w.st x.o.Z).B.host.g 0 - 1), (w.st x.o.Z).B.host.g 1 * ((w.st x.o.Z).B.host.g 1 - 1), 3 ^ 4,
      5 ^ 4] := by
    fin_cases k <;> simp
  obtain ⟨z, hz, hz'⟩ := (w.st x.o.Z).B.roots_Ks _ hmem
  have hg1 : 1 < (Dof x).host.g k := ((Dof x).host.g_prime k).one_lt
  refine ⟨⟨z ^ ((Dof x).host.g k - 1), (w.st x.o.Z).B.Ks_le (pow_mem hz _)⟩, ?_⟩
  show (w.st x.o.Z).B.embLL (z ^ ((Dof x).host.g k - 1)) = _
  rw [map_pow, hz', ← Complex.exp_nat_mul]
  congr 1
  have hc : (((Dof x).host.g k - 1 : ℕ) : ℂ) = ((Dof x).host.g k : ℂ) - 1 := by
    rw [Nat.cast_sub hg1.le, Nat.cast_one]
  have hg0 : ((Dof x).host.g k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hg1' : ((Dof x).host.g k : ℂ) - 1 ≠ 0 := by
    rw [← hc]; exact Nat.cast_ne_zero.2 (by omega)
  change (((Dof x).host.g k - 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (((Dof x).host.g k * ((Dof x).host.g k - 1) : ℕ) : ℂ)) = _
  rw [Nat.cast_mul, hc]
  field_simp

end State

theorem main : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ, (∀ kk, θ kk ≠ 1) ∧ LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ => ?_
  have hζ := fun k => roots_g x k
  choose ζ hζ using hζ
  obtain ⟨θ, hne, hlvl, hpsi⟩ := exists_theta x.m.z.pins.keep.psi ζ hζ
  exact ⟨θ, hne, hlvl, hpsi⟩

section Gen

end Gen

end GlobalTheory.HeightCounting.ThetaSt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BilinFormExistsPrimitiveOfNeZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory

theorem bilinForm_exists_primitive_of_ne_zero (X : Type) [AddCommGroup X]
    (σ : LinearMap.BilinForm ℤ X) (hσ : σ ≠ 0) :
    ∃ (g : ℕ) (β₀ : LinearMap.BilinForm ℤ X), 0 < g ∧ (g : ℤ) • β₀ = σ ∧
      ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β₀ → k = 1 := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b, σ a b ≠ 0 := by
    by_contra h
    apply hσ
    ext a b
    by_contra h'
    exact h ⟨a, b, by simpa using h'⟩
  have hbound : ∀ k : ℕ, (∃ β' : LinearMap.BilinForm ℤ X, (k : ℤ) • β' = σ) →
      k ≤ (σ a b).natAbs := by
    rintro k ⟨β', hβ'⟩
    have h1 : σ a b = (k : ℤ) * β' a b := by
      rw [← hβ']
      simp
    have h2 : k ∣ (σ a b).natAbs := Int.natCast_dvd.mp ⟨β' a b, h1⟩
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hab) h2
  let P : ℕ → Prop := fun k => ∃ β' : LinearMap.BilinForm ℤ X, (k : ℤ) • β' = σ
  have hP1 : P 1 := ⟨σ, by simp⟩
  have h1le : 1 ≤ (σ a b).natAbs := hbound 1 hP1
  have hg : P (Nat.findGreatest P (σ a b).natAbs) := Nat.findGreatest_spec h1le hP1
  have hg1 : 1 ≤ Nat.findGreatest P (σ a b).natAbs := Nat.le_findGreatest h1le hP1
  have hmax : ∀ k, P k → k ≤ Nat.findGreatest P (σ a b).natAbs :=
    fun k hk => Nat.le_findGreatest (hbound k hk) hk
  generalize Nat.findGreatest P (σ a b).natAbs = g at hg hg1 hmax
  obtain ⟨β₀, hβ₀⟩ := hg
  refine ⟨g, β₀, hg1, hβ₀, ?_⟩
  intro k β' hk
  have hgk : P (g * k) := ⟨β', by rw [Nat.cast_mul, mul_smul, hk, hβ₀]⟩
  have hle := hmax _ hgk
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hσ
    rw [← hβ₀, ← hk]
    simp
  have hk1 : k ≤ 1 := by
    have : g * k ≤ g * 1 := by simpa using hle
    exact Nat.le_of_mul_le_mul_left this hg1
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardCmTypeEmbeddingsFixingRootEqHalfFinrank
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.CMTypeCard

theorem card_psi_eq_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
  intro E _ _ _ H
  let e : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} ≃ GlobalTheory.AllWt.Psi H :=
    { toFun := fun τ => ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      invFun := fun τ => ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  have h1 : Fintype.card (E →+* ℂ) =
      Fintype.card (GlobalTheory.AllWt.Psi H) + Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).symm
  have h2 : Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} = Fintype.card (GlobalTheory.AllWt.Psi H) :=
    Fintype.card_congr e
  rw [← NumberField.Embeddings.card E ℂ, h1, h2]
  omega

end GlobalTheory.CMTypeCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimInvFunHostFixingAutInvariantStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrierDimInvFun_hostFixingAut_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)), IsTwInv H ψ → IsTwInv H (carFun H.bar ψ) := by
  first | exact @GlobalTheory.PolFan.CarDim.isTwInv_carFun | exact GlobalTheory.PolFan.CarDim.isTwInv_carFun | (intros; apply GlobalTheory.PolFan.CarDim.isTwInv_carFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGeneratorsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrierDim_le_of_add_cell_generators : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (b : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β := by
  first | exact @GlobalTheory.PolFan.carrierDim_le_of_add_cell | exact GlobalTheory.PolFan.carrierDim_le_of_add_cell | (intros; apply GlobalTheory.PolFan.carrierDim_le_of_add_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierMatrixTransferStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrier_matrix_transfer : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (s : Z ⟶ Sp O) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)), q ≫ PSpace.str O _ = f ≫ s → ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z) (α : C.A) (_ : ⊤ ≤ z ⁻¹ᵁ C.B α) (n' : ℕ) (a : Matrix (Fin n') (Fin (C.n α)) R) (a' : Matrix (Fin (C.n α)) (Fin n') R) (y : Sp K ⟶ Z') (hy : ⊤ ≤ (y ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin k → Fin (C.n α) → K), a * a' = 1 → a' * a = 1 → y ≫ f = spMap (algebraMap R K) ≫ z → Car Em f q y α hy ξ → (∀ (l : Fin k) (j : Fin n'), k ≤ (j : ℕ) → ∑ i, algebraMap R K (a j i) * ξ l i = 0) → ∃ y₀ : Sp R ⟶ PSpace O (plN N k), y₀ ≫ PSpace.str O _ = z ≫ s ∧ y ≫ q = spMap (algebraMap R K) ≫ y₀ := by
  first | exact @GlobalTheory.GrCl.IntPt.main | exact GlobalTheory.GrCl.IntPt.main | (intros; apply GlobalTheory.GrCl.IntPt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesExistsMarkedFormInCone
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem carries_exists_marked : ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) (c : FormFamily O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m : ℕ} (δ₀ : Fin m → LinearMap.BilinForm ℤ X₀) (v : LinearMap.BilinForm ℤ X₀) (t : Fin m → ℝ),
  v ∈ balForms bar X₀ → v ≠ 0 → (∀ y, 0 ≤ v y y) → c.Carries δ₀ → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), c.Carries δ →
    ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ (OrbMark.orbFun O w0 v).evalZ β = 1 ∧ InRCone δ β := by
  intro O _ bar w0 c X₀ _ _ _ m δ₀ v t hbal hv hpos hc₀ ht hsum X _ _ _ m' δ hc
  obtain ⟨e₀, s₀, hδ₀⟩ := hc₀
  obtain ⟨e, s, hδ⟩ := hc
  set g : X ≃ₗ[O] X₀ := e.trans e₀.symm with hg
  refine ⟨pull g.toLinearMap v, pull_mem _ hbal, fun y => by simpa using hpos (g y), ?_, ?_⟩
  · rw [evalZ_pull _ g.surjective]
    exact OrbMark.orbFun_evalZ_self w0 hv hbal.1
  · refine ⟨fun j => t (s₀.symm (s j)), fun j => ht _, LinearMap.ext₂ fun a b => ?_⟩
    have h1 := LinearMap.congr_fun₂ hsum (g a) (g b)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul] at h1 ⊢
    show ((v (g a) (g b) : ℤ) : ℝ) = _
    rw [h1]
    have key : ∀ i, (δ₀ i (g a) (g b) : ℝ) = (c.δ (s₀ i) (e a) (e b) : ℝ) := fun i => by
      rw [hδ₀ i, pull_apply]; simp [hg]
    have key' : ∀ j, (δ j a b : ℝ) = (c.δ (s j) (e a) (e b) : ℝ) := fun j => by
      rw [hδ j, pull_apply]; rfl
    simp only [key, key']
    rw [← (s.trans s₀.symm).sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellLeastDimVanishesWhereFormVanishesDiagonal
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

noncomputable section

namespace GlobalTheory.PolFan.Mark

theorem exists_zsmul_mem_of_finrank_le_of_le {M : Type} [AddCommGroup M] {N L : Submodule ℤ M}
    [Module.Finite ℤ L] (hNL : N ≤ L) (hr : Module.finrank ℤ L ≤ Module.finrank ℤ N) {x : M} (hx : x ∈ L) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N := by
  have h1 := Submodule.finrank_quotient_add_finrank (N.comap L.subtype)
  have h2 : Module.finrank ℤ (N.comap L.subtype) = Module.finrank ℤ N :=
    (Submodule.comapSubtypeEquivOfLe hNL).finrank_eq
  have h0 : Module.finrank ℤ (L ⧸ N.comap L.subtype) = 0 := by omega
  obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.1 h0) (Submodule.Quotient.mk ⟨x, hx⟩)
  refine ⟨a, ha, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact hax

theorem vanish_of_inRCone_of_genRank_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ τ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  intro E _ _ _ H q ψ lab hψ hlab X _ _ _ _ hX hdom m τ hτ β hβ hβp hβc hrk j y hy
  classical
  let P : Fin m → Prop := fun j => ∀ y, β y y = 0 → τ j y y = 0
  have hw : ∀ j, ∃ y, β y y = 0 ∧ (¬ P j → 0 < τ j y y) := by
    intro j
    by_cases hj : P j
    · exact ⟨0, by simp, fun h => (h hj).elim⟩
    · simp only [P, not_forall] at hj
      obtain ⟨y, hy, hne⟩ := hj
      exact ⟨y, hy, fun _ => lt_of_le_of_ne (hτ.nonneg j y) (Ne.symm hne)⟩
  choose w hw0 hwpos using hw
  let T : Finset (Fin m) := Finset.univ.filter P
  let s : Fin T.card ↪ Fin m := (T.orderEmbOfFin rfl).toEmbedding
  have hsr : Set.range s = ↑T := Finset.range_orderEmbOfFin T rfl
  have hP : ∀ k, P k ↔ k ∈ Set.range s := fun k => by rw [hsr]; simp [T]
  let hf : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ∑ i, LinearMap.applyₗ (w i) ∘ₗ LinearMap.applyₗ (w i)
  have hfa : ∀ x : LinearMap.BilinForm ℤ X, hf x = ∑ i, x (w i) (w i) := fun x => by
    simp [hf, LinearMap.sum_apply]
  have hcut : IsFaceCut τ s hf := by
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rw [hfa]; exact Finset.sum_nonneg fun i _ => hτ.nonneg k (w i)
    · rw [← hP, hfa]
      constructor
      · intro h0
        by_contra hk
        have h1 : τ k (w k) (w k) ≤ ∑ i, τ k (w i) (w i) :=
          Finset.single_le_sum (f := fun i => τ k (w i) (w i)) (fun i _ => hτ.nonneg k (w i)) (Finset.mem_univ k)
        have h2 := hwpos k hk
        omega
      · intro hk
        exact Finset.sum_eq_zero fun i _ => hk _ (hw0 i)
  have hcell : IsCell H.bar ψ (fun k => τ (s k)) :=
    isCell_face_of_isFaceCut E H q ψ hψ X hX hdom m τ hτ _ s hf hcut
  obtain ⟨c, hc, hce⟩ := hβc
  have hc0 : ∀ i, ¬ P i → c i = 0 := by
    intro i hi
    have e : (β (w i) (w i) : ℝ) = ∑ k, c k * (τ k (w i) (w i) : ℝ) := by
      have := LinearMap.congr_fun₂ hce (w i) (w i)
      simpa [LinearMap.sum_apply] using this
    rw [hw0 i, Int.cast_zero] at e
    have h1 : c i * (τ i (w i) (w i) : ℝ) ≤ ∑ k, c k * (τ k (w i) (w i) : ℝ) :=
      Finset.single_le_sum (f := fun k => c k * (τ k (w i) (w i) : ℝ))
        (fun k _ => mul_nonneg (hc k) (by exact_mod_cast hτ.nonneg k (w i))) (Finset.mem_univ i)
    have h2 : (0 : ℝ) < τ i (w i) (w i) := by exact_mod_cast hwpos i hi
    rw [← e] at h1
    nlinarith [hc i]
  have hmap : Finset.univ.map s = T := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    rw [← Set.mem_range, ← hP]
    simp [T]
  have hcone : InRCone (fun k => τ (s k)) β := by
    refine ⟨fun k => c (s k), fun k => hc _, ?_⟩
    rw [hce]
    have e1 := Finset.sum_map Finset.univ s (fun i => c i • toReal (τ i))
    rw [hmap] at e1
    rw [← e1]
    refine (Finset.sum_subset (Finset.subset_univ T) fun i _ hi => ?_).symm
    rw [hc0 i (by simpa [T] using hi), zero_smul]
  have hl := hlab X hX β hβ hβp
  have hle : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k} ≤ genRank (fun k => τ (s k)) := Nat.sInf_le ⟨_, _, hcell, hcone, rfl⟩
  have hrk' : genRank τ ≤ genRank (fun k => τ (s k)) := by
    rw [hl] at hrk
    have h4 : ((genRank τ : ℕ) : ℝ) ≤ ((genRank (fun k => τ (s k)) : ℕ) : ℝ) := hrk.trans (Nat.cast_le.2 hle)
    exact_mod_cast h4
  haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range τ)) := Module.Finite.span_of_finite ℤ (Set.finite_range τ)
  have hNL : Submodule.span ℤ (Set.range fun k => τ (s k)) ≤ Submodule.span ℤ (Set.range τ) :=
    Submodule.span_mono (Set.range_comp_subset_range s τ)
  obtain ⟨n, hn, hnmem⟩ := exists_zsmul_mem_of_finrank_le_of_le hNL hrk' (Submodule.subset_span ⟨j, rfl⟩)
  have key : ∀ x ∈ Submodule.span ℤ (Set.range fun k => τ (s k)), x y y = 0 := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact (hP (s k)).2 ⟨k, rfl⟩ y hy
    | zero => simp
    | add x z _ _ h1 h2 => simp [h1, h2]
    | smul a x _ h => simp [h]
  have h3 := key _ hnmem
  simp only [LinearMap.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_left hn

end GlobalTheory.PolFan.Mark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellOfQuotientCellRadicalPullbackStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_of_quotient_cell_radical_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolyFanOn H.bar ψ X → (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule (𝓞 E) X))), IsCell H.bar ψ δ → InRCone (fun i => pull (orad β : Submodule (𝓞 E) X).mkQ (δ i)) β → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧ genRank γ ≤ genRank δ := by
  first | exact @GlobalTheory.PolFan.CarDim.cell_of_quot_cell | exact GlobalTheory.PolFan.CarDim.cell_of_quot_cell | (intros; apply GlobalTheory.PolFan.CarDim.cell_of_quot_cell <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnIntegralTransvectionsStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trivial_on_integral_transvections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E) (s : E), ξ ∈ X.Λ → herm X.Gm ξ ξ = 0 → cc s = s → IsIntegral ℤ s → ∀ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm ξ (X.m * s * X.κ0) → φ γ = 1 := by
  first | exact @GlobalTheory.UnipKill.killsTransv | exact GlobalTheory.UnipKill.killsTransv | (intros; apply GlobalTheory.UnipKill.killsTransv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInverseRealSymmetricGramStatement
section
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_inverse_realSymmetric_gram : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, GlobalTheory.HermFrame.mddbar H z ξ η = 0) → ∀ ξ η, GlobalTheory.HermFrame.curv (fun x => (H x)⁻¹) z ξ η = -((GlobalTheory.HermFrame.conn H z η)ᵀᴴ * GlobalTheory.HermFrame.conn H z ξ)ᵀ := by
  first | exact @GlobalTheory.RealGram.curv_inv_of_real | exact GlobalTheory.RealGram.curv_inv_of_real | (intros; apply GlobalTheory.RealGram.curv_inv_of_real <;> assumption)
end

