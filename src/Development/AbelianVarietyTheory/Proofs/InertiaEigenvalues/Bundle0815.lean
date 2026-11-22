import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0807
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0531
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesCurveMulCoprime
section
noncomputable section

open CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompRat PeriodPair

namespace GlobalTheory.CompRat.Inertia

open GlobalTheory.CompRat.Weber

theorem affine_sub_mem (A : ValuationSubring ℂ) {a b x₁ x₂ y : ℂ} (m₁ : x₁ ∈ A) (my : y ∈ A)
    (h : x₁ - x₂ ∉ A.nonunits) (h₁ : a * x₁ + b - x₁ ∈ A.nonunits) (h₂ : a * x₂ + b - x₂ ∈ A.nonunits) :
    a * y + b - y ∈ A.nonunits := by
  simp only [ValuationSubring.mem_nonunits_iff, not_lt] at *
  have e₁ : A.valuation ((a - 1) * (x₁ - x₂)) < 1 := by
    rw [show (a - 1) * (x₁ - x₂) = (a * x₁ + b - x₁) - (a * x₂ + b - x₂) by ring]
    exact Valuation.map_sub_lt _ h₁ h₂
  rw [map_mul] at e₁
  have e₂ : A.valuation (a - 1) < 1 := lt_of_le_of_lt (le_mul_of_one_le_right' h) e₁
  rw [show a * y + b - y = (a * x₁ + b - x₁) + (a - 1) * (y - x₁) by ring]
  refine Valuation.map_add_lt _ h₁ ?_
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' ((A.valuation_le_one_iff _).2 (sub_mem my m₁))) e₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_zero_of_wC_eq_zero {s : ℤ × ℤ} (h : wC H s = 0) : s = 0 := by
  have hd : 0 < H.d := H.d_prime.pos
  have hs : Real.sqrt H.d ≠ 0 := by positivity
  have h2 : s.2 = 0 := by
    have := congrArg Complex.im h
    rcases cmHost_rootComplex_eq_pm_sqrt H with e | e <;> simpa [wC, e, hs, hd.ne'] using this
  have h1 : s.1 = 0 := by simpa [wC, h2] using h
  exact Prod.ext h1 h2

theorem dvd_of_div_mem {L : PeriodPair} (hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s) {k : ℕ} (hk : k ≠ 0) {s : ℤ × ℤ}
    (h : wC H s / k ∈ L.lattice) : (k : ℤ) ∣ s.1 ∧ (k : ℤ) ∣ s.2 := by
  obtain ⟨t, ht⟩ := (hL _).1 h
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [div_eq_iff hk'] at ht
  have e : (s.1 - k * t.1, s.2 - k * t.2) = (0 : ℤ × ℤ) := eq_zero_of_wC_eq_zero (H := H) (by
    simp only [wC] at ht ⊢
    push_cast
    linear_combination ht)
  exact ⟨⟨t.1, sub_eq_zero.1 (congrArg Prod.fst e)⟩, ⟨t.2, sub_eq_zero.1 (congrArg Prod.snd e)⟩⟩

theorem fixesCurve_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (m n p : ℕ) (A : ValuationSubring ℂ) (τ : ℂ ≃+* ℂ), p.Prime → (p : ℂ) ∈ A.nonunits → ¬ p ∣ n → Nat.Coprime m n → 3 ≤ m / p ^ m.factorization p → FixesCurve H τ m → (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ A → τ x - x ∈ A.nonunits) → FixesCurve H τ (m * n) := by
  rintro E _ _ _ H m n p A τ hp hA hn hmn h3 ⟨C, io, h, hfix⟩ hτ
  have hm0 : m ≠ 0 := by rintro rfl; simp at h3
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hk : ¬ p ∣ m / p ^ m.factorization p := Nat.not_dvd_ordCompl hp hm0
  have hqk : p ^ m.factorization p * (m / p ^ m.factorization p) = m := Nat.ordProj_mul_ordCompl_eq_self m p
  generalize m / p ^ m.factorization p = k at h3 hk hqk
  generalize p ^ m.factorization p = q at hqk
  have hk0 : k ≠ 0 := by omega
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hqk' : (q : ℂ) * k = m := by exact_mod_cast hqk
  have hOK := GlobalTheory.MomOne.Basic.isOK_okPair H.d H.d_prime.pos
  generalize GlobalTheory.MomOne.Basic.okPair H.d H.d_prime.pos = L at hOK
  have hL : ∀ x, x ∈ L.lattice ↔ ∃ s, x = wC H s := fun x => (hOK x).trans (exists_wC_iff H x).symm
  obtain ⟨c, hc⟩ := exists_multiplier C hL h
  obtain ⟨x, α, β, hα, hx, hint, hsep⟩ := exists_coord H.d_prime H.d_mod hOK hp A hA (N := k * n)
    fun hd => ((Nat.Prime.dvd_mul hp).1 hd).elim hk hn
  have hpt : ∀ z z', C.pt z = C.pt z' ↔ z - z' ∈ L.lattice := fun z z' => by rw [pt_eq_iff, hL]
  let T : ℂ → ℂ → Prop := fun z z' => C.pt z ≫ io = spMap (τ : ℂ →+* ℂ) ≫ C.pt z'
  have hm : ∀ a, T (wC H a / m) (wC H a / m) := fun a => by simpa [wC] using hfix a
  have h0 : T 0 0 := by simpa [wC] using hm 0
  have huniq : ∀ {z w z' w'}, T z z' → T w w' → z' - w' ∈ L.lattice → z - w ∈ L.lattice := fun {z w z' w'} a b e =>
    (hpt _ _).1 (conj_inj h (a.trans ((congrArg _ ((hpt _ _).2 e)).trans b.symm)))
  have hmul : ∀ {z z'}, T z z' → ∀ j : ℕ, T (j * z) (j * z') := fun {z z'} a j => by
    induction j with
    | zero => simpa using h0
    | succ j ih => simpa only [Nat.cast_succ, add_mul, one_mul] using conj_add h ih a
  have hkT : ∀ a, T (wC H a / k) (wC H a / k) := fun a => by
    have e : wC H ((q : ℤ) • a) / m = wC H a / k := by
      rw [← hqk'] at hm' ⊢
      have := left_ne_zero_of_mul hm'
      simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      push_cast
      field_simp
    exact e ▸ hm _
  have hkN : ∀ a, ((k * n : ℕ) : ℂ) * (wC H a / k) ∈ L.lattice := fun a => (hL _).2 ⟨(n : ℤ) • a, by
    simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    field_simp⟩
  have hnN : ∀ a, ((k * n : ℕ) : ℂ) * (wC H a / n) ∈ L.lattice := fun a => (hL _).2 ⟨(k : ℤ) • a, by
    simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    field_simp⟩
  have hnot : ∀ (j : ℤ) (z : ℂ) (b : ℤ), j = 1 ∨ j = 2 → z = wC H (j, b) / k → z ∉ L.lattice := by
    rintro j _ b hj rfl hz
    have := Int.le_of_dvd (by omega) (dvd_of_div_mem hL hk0 hz).1
    simp only at this
    omega
  have haff : ∀ z z', T z z' → z' ∉ L.lattice →
      τ (x z') = τ α * c / α * x z + (τ β - τ α * c / α * β) := fun z z' a b => by
    rw [hx, hx, map_add, map_mul, (hc z z' a b).2]
    field_simp
    ring
  generalize τ α * c / α = a at haff
  generalize τ β - a * β = b at haff
  have n₁ : wC H (1, 0) / k ∉ L.lattice := hnot 1 _ 0 (.inl rfl) rfl
  have n₂ : wC H (1, 1) / k ∉ L.lattice := hnot 1 _ 1 (.inl rfl) rfl
  have key : ∀ z z', T z z' → ((k * n : ℕ) : ℂ) * z' ∈ L.lattice → z - z' ∈ L.lattice ∨ z + z' ∈ L.lattice := by
    intro z z' t hz'
    by_cases hl : z' ∈ L.lattice
    · exact .inl (sub_mem (by simpa using huniq t h0 (by simpa using hl)) hl)
    have hz : ((k * n : ℕ) : ℂ) * z ∈ L.lattice := by simpa using huniq (hmul t (k * n)) h0 (by simpa using hz')
    have hl' := (hc z z' t hl).1
    refine hsep z z' hz hz' hl' hl ?_
    have i₁ := hint _ (hkN _) n₁
    have i₂ := hint _ (hkN _) n₂
    have e₁ := affine_sub_mem A (a := a) (b := b) (x₂ := x (wC H (1, 1) / k)) i₁.2 (hint z hz hl').2
      (fun e => (hsep _ _ (hkN _) (hkN _) n₁ n₂ e).elim (fun e' => ?_)
        (hnot 2 _ 1 (.inr rfl) (by simp only [wC]; push_cast; ring)))
      (haff _ _ (hkT _) n₁ ▸ hτ _ i₁.1 i₁.2) (haff _ _ (hkT _) n₂ ▸ hτ _ i₂.1 i₂.2)
    · have e₂ := hτ _ (hint z' hz' hl).1 (hint z' hz' hl).2
      rw [haff z z' t hl] at e₂
      rw [ValuationSubring.mem_nonunits_iff] at e₁ e₂ ⊢
      rw [show x z - x z' = (a * x z + b - x z') - (a * x z + b - x z) by ring]
      exact Valuation.map_sub_lt _ e₂ e₁
    · have e₂ : wC H (1, 0) / k - wC H (1, 1) / k = wC H (0, -1) / k := by simp only [wC]; push_cast; ring
      have := Int.le_of_dvd (by omega) (Int.dvd_neg.1 (dvd_of_div_mem hL hk0 (e₂ ▸ e')).2)
      omega
  have hnT : ∀ s, T (wC H s / n) (wC H s / n) := fun s => by
    obtain ⟨z, t⟩ := exists_conj_pt h (wC H s / n)
    suffices e : z - wC H s / n ∈ L.lattice from (congrArg (· ≫ io) ((hpt _ _).2 e)).symm.trans t
    refine (key _ _ t (hnN s)).elim id fun e => ?_
    refine (key _ _ (conj_add h t (hkT (1, 0))) (by rw [mul_add]; exact add_mem (hnN _) (hkN _))).elim
      (fun e' => by simpa using e') fun e' => ?_
    exact absurd (sub_mem e' e) (hnot 2 _ 0 (.inr rfl) (by simp only [wC]; push_cast; ring))
  refine ⟨C, io, h, fun s => ?_⟩
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hmn
  have huv' : (u : ℂ) * m + v * n = 1 := by exact_mod_cast huv
  have e : wC H s / (m * n : ℕ) = wC H (v • s) / m + wC H (u • s) / n := by
    simp only [wC, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    field_simp
    linear_combination -(s.1 * 2 + s.2 * (1 + H.rt0)) * huv'
  rw [show wC H (1, 0) = 1 by simp [wC], one_mul, e]
  exact conj_add h (hm _) (hnT _)

end GlobalTheory.CompRat.Inertia
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormReadingEqGoodModelVectorEvaluation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SeriesTie.ModelGood

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)

def jH (j : Fin D.R.m) : S.WL ((j : ℕ) + 1) →+ (Rl.HW j (sg0 D A3.A)).H where
  toFun x := (Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x)
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]

theorem jH_smul (j : Fin D.R.m) (c : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    jH YS j (c • x) = D.what₂.embLL c • jH YS j x := by
  change (Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (c • x)) = _
  rw [map_smul, map_smulₛₗ, show sg0 D A3.A c = D.what₂.embLL c from
    congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)]
  rfl

section Read

variable {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

def evH : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1) →+ (Rl.HW j (sg0 D A3.A)).H :=
  TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ρ.e i b a)).comp
        ((jH YS j).comp (S.A ((j : ℕ) + 1)).WK.subtype.toAddMonoidHom)
      map_zero' := by ext; simp [show ρ.e i b (0 : NX.KB S i b) = 0 from map_zero _]
      map_add' := fun x y => by
        ext; simp [show ρ.e i b (x + y : NX.KB S i b) = ρ.e i b x + ρ.e i b y from map_add _ _ _, add_smul] }
    fun c a f => by
      change ρ.e i b (sideEmb D.ntw i b (S.kKs c) * (show FractionRing (D.ntw.O i) from a)) • jH YS j (Subtype.val f) =
        ρ.e i b a • jH YS j (c • Subtype.val f)
      rw [← algebraMap_smul D.what₂.LL c, jH_smul, map_mul, hρ.e_LL0, smul_smul, mul_comm, ← S.kKs_spec]
      rfl

theorem evH_tmul (a : NX.KB S i b) (f : NX.FmK S ((j : ℕ) + 1)) :
    evH YS hρ i j b (a ⊗ₜ f) = ρ.e i b a • jH YS j (Subtype.val f) := rfl

theorem evK_eq (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b t = (Rl.HW j (sg0 D A3.A)).e (evH YS hρ i j b t) (v₀ j _) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; rfl
  | tmul a f => rw [evK_tmul, evH_tmul, map_smul]; rfl

theorem evH_smul (c : NX.KB S i b) (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evH YS hρ i j b (c • t) = ρ.e i b c • evH YS hρ i j b t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul a f =>
    rw [TensorProduct.smul_tmul', evH_tmul, evH_tmul, smul_smul]
    exact congrArg (· • _) (map_mul (ρ.e i b) c a)

def mv (y : D.nexp.Fm i ((j : ℕ) + 1) b) : (Rl.HW j (sg0 D A3.A)).H :=
  evH YS hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 y)

theorem mv_act (hU : Rl.toRealDat.LUnif) (g : G0g D.nd) (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b (D.nexp.actG i _ b g y)) =
      postOn _ (actL (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm g))
        ((Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b y)) := by
  unfold mv
  rw [YS.act]
  generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 y = t
  induction t using TensorProduct.induction_on with
  | zero =>
    erw [LinearEquiv.map_zero]
    simp only [map_zero]
    exact (congrArg (Rl.HW j (sg0 D A3.A)).e ((evH YS hρ i j b).map_zero)).trans (map_zero _)
  | add y z hy hz => erw [LinearEquiv.map_add, map_add, map_add, hy, hz, map_add, map_add, map_add]
  | tmul a f0 =>
    have e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g)
        (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ
          (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0) := by
      change (NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ •
        (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    erw [e1]
    rw [evH_tmul, evH_tmul]
    have hgeq : Rl.eG ((YS.fi j).eG (S.eG.symm g)) = cG.symm g := by
      have h0 := YS.geq j (S.eG.symm g)
      rw [MulEquiv.apply_symm_apply] at h0
      exact ((MulEquiv.symm_apply_eq cG).2 h0.symm).symm
    have he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) =
        D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) :=
      hρ.e_LL0 i b _
    have hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    have hs : sg0 D A3.A = D.what₂.embLL := GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl
    change (Rl.HW j (sg0 D A3.A)).e (ρ.e i b _ • (Rl.FW j).j (sg0 D A3.A)
      ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)))) = _
    rw [map_smul, map_smul, map_smul, (YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi, hgeq, smul_smul]
    congr 1
    erw [map_mul, map_inv₀, he, hs]
    field_simp

theorem mv_smul (c : FractionRing (D.ntw.O i)) (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    mv YS hρ i j b (c • y) = ρ.e i b c • mv YS hρ i j b y := by
  unfold mv
  rw [map_smul]
  exact evH_smul YS hρ i j b c _

theorem mv_sum {ι : Type} (s : Finset ι) (y : ι → D.nexp.Fm i ((j : ℕ) + 1) b) :
    mv YS hρ i j b (∑ k ∈ s, y k) = ∑ k ∈ s, mv YS hρ i j b (y k) := by
  unfold mv
  rw [map_sum]
  exact map_sum (evH YS hρ i j b) _ _

theorem postOn_eWf_sum (σ : D.what₂.LL →+* ℂ) (M : MMap (Rl.MW j σ)) :
    postOn (Rl.MW j σ) (Rl.toRealDat.eWf j σ) M = ∑ γ : Γ, RealDat.eC (A := A3.A) σ γ •
      postOn (Rl.MW j σ) (actL (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG γ)) M := by
  refine MultilinearMap.ext fun v => ?_
  simp only [RealDat.eWf, gaL, postOn, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compMultilinearMap_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply, MultilinearMap.smul_apply]
  rfl

theorem mv_eG (hU : Rl.toRealDat.LUnif)
    (hid : ∀ γ : Γ, D.what₂.embLL ((idemOf A3.A.X).coeff γ) = D.ntypes.e0.coeff ((Rl.eG.trans cG) γ))
    (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b y)) =
      postOn _ (Rl.toRealDat.eWf j (sg0 D A3.A)) ((Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b y)) := by
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv Γ (Rl.eG.trans cG).toEquiv
  have h1 : Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b y = ∑ g, (D.nexp.eAlg i b).coeff g • D.nexp.actG i _ b g y := by
    unfold Formalism.MainNotions.IntegralHeckeForms.eG
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype]
    · rw [LinearMap.sum_apply]; rfl
    · intro; exact zero_smul _ _
  have hc : ∀ g, ρ.e i b ((D.nexp.eAlg i b).coeff g) = D.ntypes.e0.coeff g := fun g => by
    have h : (D.nexp.eAlg i b).coeff g = NX.readLL0 S i b (D.nexp.eLL0 g) := by rw [D.nexp.eAlg_def]; rfl
    rw [h]
    exact (hρ.e_LL0 i b _).trans (D.nStage_trivialCharacter_coeff_eq g)
  have hs : sg0 D A3.A = D.what₂.embLL := GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl
  rw [h1, mv_sum, map_sum, postOn_eWf_sum]
  refine (Fintype.sum_equiv (Rl.eG.trans cG).toEquiv _ _ fun γ => ?_).symm
  rw [mv_smul, map_smul, mv_act YS hρ i j b hU, hc]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  congr 1
  exact (congrArg (fun f : D.what₂.LL →+* ℂ => f ((idemOf A3.A.X).coeff γ)) hs).trans (hid γ)

end Read
end GlobalTheory.SeriesTie.ModelGood

open GlobalTheory.SeriesTie.ModelGood in
theorem GlobalTheory.SeriesTie.rd_good_model : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∃ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      Y.Z.rd i j b x = (Y.Z.ν i j b)⁻¹ • (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) := by
  intro D X E Y i j b x hx
  obtain ⟨f, -, rfl⟩ := hx
  have hidem : ∀ z, Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b z) = Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i ((j : ℕ) + 1) b z :=
    fun z => by rw [← Module.End.mul_apply, Formalism.MainNotions.IntegralHeckeForms.eG, ← map_mul, D.nexp.eAlg_idem]
  refine ⟨mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f), ⟨?_, ?_⟩, ?_⟩
  · have h := LinearMap.mem_range_self (X.R.HW j (sg0 D X.A3.A)).e
      (mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f))
    rw [(X.char.models.HW j _).2.1] at h
    exact h
  · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]
    rw [← mv_eG Y.YS Y.Z.good i j b X.unif X.idem, hidem]
  · change (Y.Z.ν i j b)⁻¹ • evK Y.YS X.geo.v₀ Y.Z.good i j b _ = _
    exact congrArg _ (evK_eq Y.YS Y.Z.good i j b X.geo.v₀ _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodIdempotentIrreducibleCharacterGenericSumNeZe
section
open Formalism.BasicNotions GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.WhittakerMeets

open Formalism.L2.DIV GlobalTheory.FinGL

def addOf {p : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) : AddChar (ZMod p) ℂ where
  toFun a := (θ (Multiplicative.ofAdd a) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [ofAdd_add]

theorem addOf_ne_one {p : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) (h : θ ≠ 1) : addOf θ ≠ 1 := by
  intro h1
  apply h
  refine MonoidHom.ext fun z => Units.ext ?_
  have h2 : addOf θ (Multiplicative.toAdd z) = 1 := by rw [h1]; rfl
  exact h2

theorem addCharHom_addOf {p r : ℕ} (θ : Multiplicative (ZMod p) →* ℂˣ) (h : unip (ZMod p) r) :
    ((addCharHom (addOf θ) (supHom (ZMod p) r) h : ℂˣ) : ℂ) =
      (θ (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))) : ℂ) :=
  rfl

theorem local_sum_ne_zero {p : ℕ} [hp : Fact p.Prime] {r : ℕ} [Fintype (unip (ZMod p) r)] (θ : GL (Fin r) (ZMod p) → ℂ)
    (hθ : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar θ) (θ' : Multiplicative (ZMod p) →* ℂˣ) (h' : θ' ≠ 1) :
    ∑ h : unip (ZMod p) r, θ h *
      (((θ' (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))))⁻¹ : ℂˣ) : ℂ)
      ≠ 0 := by
  obtain ⟨d, b, σ, hσ, hθe⟩ := hθ
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.finite_parInd (F := ZMod p) b σ
  have h1 := GlobalTheory.GenericProduct.sum_unip_eq (addOf θ') (parInd b σ)
  rw [GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one (ZMod p) (addOf θ') (addOf_ne_one θ' h') r _ b σ hσ, Nat.cast_one, mul_one] at h1
  have e : ∀ h : unip (ZMod p) r, θ h *
      (((θ' (Multiplicative.ofAdd (Formalism.L2.NX.supSum r ((h : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)))))⁻¹ : ℂˣ) : ℂ) =
      LinearMap.trace ℂ _ (parInd b σ h) * (((addCharHom (addOf θ') (supHom (ZMod p) r) h)⁻¹ : ℂˣ) : ℂ) := by
    intro h
    rw [hθe, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, addCharHom_addOf]
    rfl
  rw [Finset.sum_congr rfl fun h _ => e h, h1]
  exact Nat.cast_ne_zero.2 Nat.card_pos.ne'

end GlobalTheory.WhittakerMeets

namespace GlobalTheory.WhittakerMeets

open Formalism.L2.DIV GlobalTheory.FinGL

theorem sum_ne_zero : ∀ (D : D7), GrpSide D → ∀ [Fintype (G0g D.nd)] (U : Subgroup (G0g D.nd)) [Fintype U], U = Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r → ∀ ψ : U →* ℂˣ, Formalism.L2.NX.IsStdGeneric (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ψ → 2 ≤ D.R.r → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0 := by
  intro D S _ U _ hU ψ hψ hr χ hχ he
  classical
  subst hU
  haveI hF : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fact (D.host.g kv.1).Prime := fun kv => ⟨D.host.g_prime kv.1⟩
  haveI hN : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), NeZero (D.host.g kv.1) := fun kv => ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨θ, hθ, hχe⟩ := GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product D (fun k => ⟨_, S.O k, S.eSer_def k⟩) χ hχ he
  obtain ⟨θ', hθ'1, hψe⟩ := hψ
  have hθ' := hθ'1 hr
  letI : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fintype (unip (ZMod (D.host.g kv.1)) D.R.r) := fun kv => Fintype.ofFinite _
  let f : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), unip (ZMod (D.host.g kv.1)) D.R.r → ℂ := fun kv h =>
    θ kv h * (((θ' kv (Multiplicative.ofAdd (Formalism.L2.NX.supSum D.R.r
      ((h : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))))⁻¹ : ℂˣ) : ℂ)
  let e : Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r ≃
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), unip (ZMod (D.host.g kv.1)) D.R.r :=
    { toFun := fun u kv => ⟨u.1 kv, (u.2 kv).1, (u.2 kv).2⟩
      invFun := fun y => ⟨fun kv => (y kv).1, fun kv => ⟨(y kv).2.1, (y kv).2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hterm : ∀ u : Formalism.L2.NX.Uup (fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) D.R.r,
      χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) = ∏ kv, f kv (e u kv) := by
    intro u
    rw [hχe, hψe, Formalism.L2.NX.stdVal, ← Finset.prod_inv_distrib, Units.coe_prod, ← Finset.prod_mul_distrib]
    rfl
  rw [Finset.sum_congr rfl fun u _ => hterm u, Fintype.sum_equiv e _ (fun y => ∏ kv, f kv (y kv)) fun _ => rfl,
    ← Fintype.prod_sum]
  exact Finset.prod_ne_zero_iff.2 fun kv _ => local_sum_ne_zero (θ kv) (hθ kv) (θ' kv) (hθ' kv)

end GlobalTheory.WhittakerMeets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralOfIsSubquotientProdIrr
section
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT

namespace GlobalTheory.RecT

theorem geometricLemma_holds : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_holds

theorem good_toral_of_isSubquotient_prodIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : ℕ) (y : Fin t → IrrGL k) (x : IrrGL k) (hd : ∑ i, (y i).1 = x.1),
    IsSubquotient x.rep (prodIrr y hd) → (Good x → ∀ i, Good (y i)) ∧ (Toral x → ∀ i, Toral (y i)) ∧
      ((∀ i, Good (y i)) → Good x) ∧ ((∀ i, Toral (y i)) → Toral x) := by
  intro k _ _ _ _ t y x hd hsq
  have hG := geometricLemma_holds
  have hBZ := GlobalTheory.bernsteinZelevinskyFiniteness_holds
  choose s hs using fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG (y i)
  have hx : HasSupport x.rep (∑ i, s i) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hs x.2.rep.irr hsq

  have down : ∀ P : IrrGL k → Prop, (∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z) →
      ∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z := by
    rintro P ⟨u, hu, hP⟩ i
    have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hu hx
    exact ⟨s i, hs i, fun z hz => hP z (this ▸ Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hz⟩)⟩

  have up : ∀ P : IrrGL k → Prop, (∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z) →
      ∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z := by
    intro P h
    choose u hu hP using h
    refine ⟨∑ i, u i, GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hu x.2.rep.irr hsq, fun z hz => ?_⟩
    obtain ⟨i, -, hz⟩ := Multiset.mem_sum.1 hz
    exact hP i z hz
  exact ⟨down _, down _, up _, up _⟩

end GlobalTheory.RecT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsFurther
section
namespace GlobalTheory.ScalarMultipleMembership

theorem exists_smul_mem {Ks WL : Type} [Field Ks] [NumberField Ks] [AddCommGroup WL] [Module Ks WL]
    [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL]
    (M : Submodule (NumberField.RingOfIntegers Ks) WL) (x : WL)
    (hx : x ∈ Submodule.span Ks (M : Set WL)) :
    ∃ a : NumberField.RingOfIntegers Ks, a ≠ 0 ∧ a • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem b hay
    · rw [mul_smul]; exact M.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨n, d, hd, hc⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers Ks) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap (NumberField.RingOfIntegers Ks) Ks d ≠ 0 := by
      intro h
      exact hd0 (IsFractionRing.injective (NumberField.RingOfIntegers Ks) Ks (by simpa using h))
    refine ⟨a * d, mul_ne_zero ha hd0, ?_⟩
    have key : (a * d) • c • y = n • a • y := by
      rw [← algebraMap_smul Ks (a * d), ← algebraMap_smul Ks n, ← algebraMap_smul Ks a,
        smul_smul, smul_smul, ← hc, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem n hay

theorem main {LL Ks WL G : Type} [inst : Field LL] [NumberField LL] [inst_2 : Field Ks] [inst_3 : NumberField Ks] [inst_4 : Algebra Ks LL] [inst_5 : AddCommGroup WL] [inst_6 : Module LL WL] [inst_7 : Module Ks WL] [IsScalarTower Ks LL WL] [inst_9 : Module (NumberField.RingOfIntegers Ks) WL] [inst_10 : IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {W : (LL →+* ℂ) → Type} [inst_11 : (σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [inst_12 : (σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [inst_13 : Group G] (Φ : Formalism.IndefR.Arith.FormsL LL Ks WL W G)
    (h : Submodule.span Ks (↑(Formalism.IndefR.Arith.FormsL.MK Φ) : Set WL) = Formalism.IndefR.Arith.FormsL.WK Φ) :
    ∀ x ∈ Formalism.IndefR.Arith.FormsL.WK Φ, ∃ (a : NumberField.RingOfIntegers Ks), a ≠ (0 : NumberField.RingOfIntegers Ks) ∧ a • x ∈ Formalism.IndefR.Arith.FormsL.MK Φ := by
  intro x hx
  rw [← h] at hx
  exact exists_smul_mem _ x hx

end GlobalTheory.ScalarMultipleMembership
end

