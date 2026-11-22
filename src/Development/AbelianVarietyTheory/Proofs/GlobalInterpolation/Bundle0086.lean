import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.UniqInvHolds

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable

section Inputs

open Formalism.MainNotions.TaylorLogMetric

def goodLifts (D : D7) (T : Tor D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AddSubgroup (VC D N N') :=
  AddSubgroup.closure {y | ∃ κ : 𝓞 D.host.K,
    ‖lamC lam (D.host.φ₀ (D.host.conj ((κ : D.host.K) : D.host.E)))‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧
    ∃ x ∈ La D T L L', y = (D.host.φ₀ ((κ : D.host.K) : D.host.E) * (N₀ : ℂ) / (p : ℂ) ^ n) • x}

def MomentsAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (Ω : ℂ_[p]) : Prop :=
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D p (La D (tor0 D cc δ) L L') t →
    ∃ N₀ : ℕ, Nat.Coprime N₀ p ∧
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), NNBasis D (tor0 D cc δ) δ p L L' b →
    ∃ μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p], ‖μ‖ ≤ 1 ∧
      ∀ (n : ℕ), ∀ y ∈ goodLifts D (tor0 D cc δ) lam N₀ n L L',
        CoefIn D (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (e N N' L L'))) Qbar ∧
        ∀ (m : ℕ) (y' : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
          (∀ a : Fin r → ℕ, g (fun i => (a i : ℤ_[p])) =
            lamC lam (kap D (tor0 D cc δ) (δ • embV D (tor0 D cc δ) (∑ i, (a i : D.host.E) • b i)) y) *
              ∏ j, pairN D lam Ω b (y' j) fun i => (a i : ℤ_[p])) →
          jet D lam y' (pSer D lam (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (e N N' L L')))) = μ g

def TranslateMoments (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → Nat.Coprime (Ideal.absNorm cc) p →
    ∃ Ω : ℂ_[p], IsOmP lam (tor0 D cc δ).abelian₂ Ω ∧ MomentsAt D cc δ e lam Ω

def TranslateMomentsAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → TranslateMoments D cc δ (B.eNat χ)

def MovesAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ

def LatticeFactsAll : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ →
    ∀ a b : ℕ, Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b

end Inputs

section Ops

variable {X : Fields} (A : Amb X) {a b : ℕ}

def emb (x : HomE X.E a b) : VCx X.Tau a b := embH (X.embC A.σ₀) A.δ x

def Wx (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ) : VCx X.Tau a b → ℂ :=
  fun z => alV A.d A.sc (emb A x) * opU (HV A.sc) (emb A x) F z

def imH (x y : HomE X.E a b) : ℝ := altE (HV A.sc) (emb A x) (emb A y)

def coc (x y : HomE X.E a b) : ℝ := (Real.sqrt A.d * (HV A.sc (emb A x) (emb A y)).re + imH A x y) / 2

def brkE (y t : HomE X.E a b) : ℂ := brk (HV A.sc) (emb A y) (emb A t)

abbrev per (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Submodule (𝓞 X.E) (HomE X.E a b) :=
  perO A.AA N N'

def smulLat (r : X.E) (M : Submodule (𝓞 X.E) (HomE X.E a b)) : Submodule (𝓞 X.E) (HomE X.E a b) :=
  M.map ((r • (LinearMap.id : HomE X.E a b →ₗ[X.E] HomE X.E a b)).restrictScalars (𝓞 X.E))

theorem mem_smulLat (r : X.E) (M : Submodule (𝓞 X.E) (HomE X.E a b)) (y : HomE X.E a b) :
    y ∈ smulLat r M ↔ ∃ m ∈ M, r • m = y := Iff.rfl

variable (a b) in

def PtMom {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]) (v : X.E) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    ∀ t : HomE X.E a b, (∃ n : ℕ, Nat.Coprime n p ∧ (n : X.E) • t ∈ per A N N') →
    ∃ N₀ : ℕ, Nat.Coprime N₀ p ∧
      (∀ y ∈ per A N N', ∀ m, jetC A.cD (Wx A (((N₀ : X.E) * v) • y) (Wx A t (A.e a b N N'))) m ∈ TaylorLogMetric.Qbar) ∧
      InIntClosure (per A N N' : Set (HomE X.E a b))
        (fun x (k : HomE X.E a b × (DVar X.Tau a b →₀ ℕ)) =>
          TaylorLogMetric.lamC lam (brkE A (((N₀ : X.E) * v) • k.1) x) * ptTab ι un x k.2)
        {k | k.1 ∈ per A N N'}
        fun k => TaylorLogMetric.lamC lam (jetC A.cD (Wx A (((N₀ : X.E) * v) • k.1) (Wx A t (A.e a b N N'))) k.2)

variable (a b) in

def Ctx (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) : Prop :=
  X.Ok ∧ A.LaHyp a b S ∧ A.AAUnit (divs (X.conjO ϖ)) ∧ A.ESmooth a b ∧ p.Prime ∧ ϖ * X.conjO ϖ = (p : 𝓞 X.E) ∧
    IsCoprime ϖ (X.conjO ϖ) ∧ (∀ P, P ∈ S ↔ ϖ ∈ P.asIdeal ∨ P ∈ SG) ∧ (∀ P ∈ SG, (p : 𝓞 X.E) ∉ P.asIdeal) ∧
    Nat.Coprime g p ∧ Nat.Coprime cA p

end Ops

section Clo

variable {p : ℕ} [Fact p.Prime] {H I : Type}

theorem clo_zero (Sup : Set H) (tab : H → I → ℂ_[p]) (M : Set I) : InIntClosure Sup tab M fun _ => 0 := by
  intro F _ ε hε
  exact ⟨0, by simp, by simp, by simpa using fun _ _ => hε⟩

theorem clo_add {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J J' : I → ℂ_[p]}
    (h : InIntClosure Sup tab M J) (h' : InIntClosure Sup tab M J') : InIntClosure Sup tab M fun m => J m + J' m := by
  classical
  intro F hF ε hε
  obtain ⟨c, hc, hc1, hcF⟩ := h F hF ε hε
  obtain ⟨c', hc', hc1', hcF'⟩ := h' F hF ε hε
  refine ⟨c + c', ?_, fun x => ?_, fun m hm => ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 (Finsupp.support_add (Finset.mem_coe.1 hx)) with h | h
    exacts [hc h, hc' h]
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc1 x) (hc1' x))
  · rw [Finsupp.sum_add_index' (by simp) (by intros; ring)]
    have : J m + J' m - ((c.sum fun x r => r * tab x m) + c'.sum fun x r => r * tab x m) =
        (J m - c.sum fun x r => r * tab x m) + (J' m - c'.sum fun x r => r * tab x m) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hcF m hm) (hcF' m hm))

theorem clo_sum {κ : Type} {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} (s : Finset κ) (J : κ → I → ℂ_[p])
    (h : ∀ k ∈ s, InIntClosure Sup tab M (J k)) : InIntClosure Sup tab M fun m => ∑ k ∈ s, J k m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using clo_zero Sup tab M
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact clo_add (h k (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem clo_congr {Sup Sup' : Set H} {tab : H → I → ℂ_[p]} {M M' : Set I} {J J' : I → ℂ_[p]}
    (h : InIntClosure Sup tab M J) (hS : Sup ⊆ Sup') (hM : M' ⊆ M) (hJ : ∀ m ∈ M', J' m = J m) :
    InIntClosure Sup' tab M' J' := by
  intro F hF ε hε
  obtain ⟨c, hc, hc1, hcF⟩ := h F (hF.trans hM) ε hε
  exact ⟨c, hc.trans hS, hc1, fun m hm => by rw [hJ m (hF hm)]; exact hcF m hm⟩

theorem clo_comb {I' κ : Type} {Sup Sup' : Set H} {tab : H → I → ℂ_[p]} {tab' : H → I' → ℂ_[p]} {M : Set I} {M' : Set I'}
    {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J) (s : Finset κ) (r : κ → I' → ℂ_[p]) (φ : κ → I' → I)
    (hφ : ∀ k ∈ s, ∀ m ∈ M', φ k m ∈ M) (w : H → ℂ_[p]) (hw : ∀ x ∈ Sup, ‖w x‖ ≤ 1) (hw0 : ∀ x ∈ Sup, x ∉ Sup' → w x = 0)
    (htab : ∀ x ∈ Sup, ∀ m ∈ M', ∑ k ∈ s, r k m * tab x (φ k m) = w x * tab' x m) :
    InIntClosure Sup' tab' M' fun m => ∑ k ∈ s, r k m * J (φ k m) := by
  classical
  intro F hF ε hε
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ k ∈ s, ∀ m ∈ F, ‖r k m‖ ≤ C := by
    refine ⟨1 + ∑ q ∈ s ×ˢ F, ‖r q.1 q.2‖, by positivity, fun k hk m hm => ?_⟩
    have := Finset.single_le_sum (f := fun q : κ × I' => ‖r q.1 q.2‖) (fun _ _ => norm_nonneg _)
      (Finset.mk_mem_product hk hm)
    linarith
  obtain ⟨c, hc, hc1, hcF⟩ := h ((s ×ˢ F).image fun q => φ q.1 q.2) (by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi)
    exact hφ _ (Finset.mem_product.1 hq).1 _ (hF (Finset.mem_product.1 hq).2)) (ε / 2 / C) (by positivity)
  have hmem : ∀ x, c x ≠ 0 → x ∈ Sup := fun x hx => hc (Finsupp.mem_support_iff.2 hx)
  refine ⟨Finsupp.onFinset c.support (fun x => c x * w x) (fun x hx => Finsupp.mem_support_iff.2 (left_ne_zero_of_mul hx)),
    ?_, fun x => ?_, fun m hm => ?_⟩
  · intro x hx
    have hx' : c x * w x ≠ 0 := by simpa using hx
    by_contra hn
    exact hx' (by rw [hw0 x (hmem x (left_ne_zero_of_mul hx')) hn, mul_zero])
  · rw [Finsupp.onFinset_apply]
    by_cases hx : c x = 0
    · simp [hx]
    · rw [norm_mul]; exact mul_le_one₀ (hc1 x) (norm_nonneg _) (hw x (hmem x hx))
  · rw [Finsupp.onFinset_sum _ (by simp)]
    have e : ∑ k ∈ s, r k m * J (φ k m) - ∑ x ∈ c.support, c x * w x * tab' x m =
        ∑ k ∈ s, r k m * (J (φ k m) - c.sum fun x q => q * tab x (φ k m)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finsupp.sum, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [mul_assoc, ← htab x (hc hx) m (hF hm), Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (C := ε / 2) (by positivity) fun k hk => ?_)
      (by linarith)
    rw [norm_mul]
    have h1 := hcF (φ k m) (Finset.mem_image.2 ⟨(k, m), Finset.mk_mem_product hk hm, rfl⟩)
    calc _ ≤ C * (ε / 2 / C) := mul_le_mul (hC k hk m hm) h1.le (norm_nonneg _) hC0.le
      _ = ε / 2 := by field_simp

theorem clo_smul {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J)
    (r c : ℂ_[p]) (hc : c ≠ 0) (hr : ‖r‖ ≤ ‖c‖) :
    InIntClosure Sup (fun x m => c * tab x m) M fun m => r * J m := by
  have := clo_comb (Sup' := Sup) (tab' := fun x m => c * tab x m) (M' := M) h ({()} : Finset Unit) (fun _ _ => r) (fun _ m => m)
    (fun _ _ _ hm => hm) (fun _ => r / c)
    (fun _ _ => by rw [norm_div]; exact div_le_one_of_le₀ hr (norm_nonneg _)) (fun _ h h' => absurd h h')
    (fun x _ m _ => by simp only [Finset.sum_singleton]; field_simp)
  simpa using this

theorem clo_mul {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J)
    (r : ℂ_[p]) (hr : ‖r‖ ≤ 1) : InIntClosure Sup tab M fun m => r * J m := by
  simpa using clo_smul h r 1 one_ne_zero (by simpa using hr)

end Clo

end GlobalTheory.MomT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UniformizationHolds
section
noncomputable section

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

abbrev cj : ℂ →+ ℂ := (starRingEnd ℂ).toAddMonoidHom

theorem cj_apply (z : ℂ) : cj z = starRingEnd ℂ z := rfl

theorem map_cj_map_cj (Λ : AddSubgroup ℂ) : (Λ.map cj).map cj = Λ := by
  rw [AddSubgroup.map_map]
  have : cj.comp cj = AddMonoidHom.id ℂ := by ext z; simp [cj_apply]
  rw [this, AddSubgroup.map_id]

theorem eisG_map_cj (Λ : AddSubgroup ℂ) (k : ℕ) :
    eisG (Λ.map cj) k = starRingEnd ℂ (eisG Λ k) := by
  unfold eisG
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ.map cj ∧ w ≠ 0} :=
    { toFun := fun w => ⟨starRingEnd ℂ w.1, ⟨w.1, w.2.1, rfl⟩, by simpa using w.2.2⟩
      invFun := fun w => ⟨starRingEnd ℂ w.1, by
          obtain ⟨v, hv, hv'⟩ := AddSubgroup.mem_map.1 w.2.1
          have : starRingEnd ℂ w.1 = v := by rw [← hv']; simp [cj_apply]
          rw [this]; exact hv, by simpa using w.2.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  rw [← e.tsum_eq, Complex.conj_tsum]
  congr 1
  ext w
  show (1 : ℂ) / (starRingEnd ℂ (w : ℂ)) ^ (2 * k) = starRingEnd ℂ (1 / (w : ℂ) ^ (2 * k))
  simp [map_div₀, map_pow]

theorem eisenstein_g_two_map_conj (Λ : AddSubgroup ℂ) : g2 (Λ.map cj) = starRingEnd ℂ (g2 Λ) := by
  unfold g2; rw [eisG_map_cj, map_mul, map_ofNat]

theorem eisenstein_g_three_map_conj (Λ : AddSubgroup ℂ) : g3 (Λ.map cj) = starRingEnd ℂ (g3 Λ) := by
  unfold g3; rw [eisG_map_cj, map_mul, map_ofNat]

theorem discr_map_cj (Λ : AddSubgroup ℂ) :
    Formalism.MainNotions.TaylorLogMetric.discr (Λ.map cj) = starRingEnd ℂ (Formalism.MainNotions.TaylorLogMetric.discr Λ) := by
  unfold Formalism.MainNotions.TaylorLogMetric.discr; rw [eisenstein_g_two_map_conj, eisenstein_g_three_map_conj, map_sub, map_mul, map_pow, map_pow, map_ofNat]

theorem lamConj_spec (hU : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization) (M : IntermediateField ℚ ℂ)
    (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) (h1 : Formalism.MainNotions.TaylorLogMetric.discr Λ = 1) :
    g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ ∧ g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ ∧
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ Λ) = 1 := by
  have hl2 : liftM M (g2 Λ) = ⟨g2 Λ, h2⟩ := dif_pos h2
  have hl3 : liftM M (g3 Λ) = ⟨g3 Λ, h3⟩ := dif_pos h3
  have hdM : (⟨g2 Λ, h2⟩ : M) ^ 3 - 27 * (⟨g3 Λ, h3⟩ : M) ^ 2 = 1 := by
    apply M.val.injective
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]
    exact h1
  have hab : (ρ ⟨g2 Λ, h2⟩) ^ 3 - 27 * (ρ ⟨g3 Λ, h3⟩) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hdM, map_one]
  obtain ⟨Λ', -, h2', h3'⟩ := (hU _ _ (by rw [hab]; exact one_ne_zero)).1
  have hex : ∃ Λ' : AddSubgroup ℂ, g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)) :=
    ⟨Λ', by rw [hl2]; exact h2', by rw [hl3]; exact h3'⟩
  have hs := Classical.epsilon_spec hex
  have e2 : g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ := hs.1.trans (by rw [hl2])
  have e3 : g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ := hs.2.trans (by rw [hl3])
  refine ⟨e2, e3, ?_⟩
  show g2 _ ^ 3 - 27 * g3 _ ^ 2 = 1
  rw [e2, e3, hab]

def conjO (D : D7) : 𝓞 D.host.K ≃+* 𝓞 D.host.K :=
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  RingOfIntegers.mapRingEquiv
    ((AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K ≃ₐ[ℚ] D.host.K) : D.host.K ≃+* D.host.K)

theorem phi_conjO (D : D7) (a : 𝓞 D.host.K) :
    D.host.φ₀ (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      starRingEnd ℂ (D.host.φ₀ ((a : D.host.K) : D.host.E)) := by
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  have h : (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
    rw [conjO, RingOfIntegers.mapRingEquiv_apply]
    exact AlgEquiv.restrictNormal_commutes D.host.conj D.host.K (a : D.host.K)
  rw [h]
  exact D.host.toHostAx.conjE_apply _ _

theorem lamOf_map_cj (D : D7) (c : Ideal (𝓞 D.host.K)) (x : ℂ) :
    (lamOf D c x).map cj = lamOf D (c.map (conjO D)) (starRingEnd ℂ x) := by
  unfold lamOf
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨conjO D a, Ideal.mem_map_of_mem _ ha, ?_⟩
    rw [phi_conjO, cj_apply, map_mul]
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_map_of_equiv] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨_, ⟨a, ha, rfl⟩, by rw [phi_conjO, cj_apply, map_mul]⟩

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem containsData {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {M : IntermediateField ℚ ℂ}
    (h : DataIn D (tor0 D cc δ) M) : EquidistributedConjugates.ContainsData D M (lamOf D cc δ) := by
  refine ⟨fun x => ?_, h.2.1, h.2.2⟩
  have := h.1 (D.eTau.symm 1) (x : D.host.E)
  rwa [show (tor0 D cc δ).emb (D.eTau.symm 1) (x : D.host.E) = embT D (D.eTau.symm 1) (x : D.host.E) from rfl,
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D _ _ x.2] at this

theorem conj_lattice : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization →
    EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  intro hU hCE _ D cc δ M _ t hS ρ
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have h2 : g2 (lamOf D cc δ) ∈ M := hM.2.1
  have h3 : g3 (lamOf D cc δ) ∈ M := hM.2.2
  have hsp := fun ρ' => lamConj_spec hU M ρ' (lamOf D cc δ) h2 h3 h1
  refine ⟨(hsp ρ).2.2, ?_⟩
  obtain ⟨⟨c, hcH, -⟩, hC2, -⟩ := hCE D cc δ hcc hδ M (containsData hM)
  by_cases hρ : EquidistributedConjugates.FixesK D M ρ
  · obtain ⟨x, hx, hxe⟩ := hcH ⟨ρ, hρ⟩
    exact ⟨_, nonZeroDivisors.coe_ne_zero _, x, hx, hxe⟩
  · obtain ⟨hρ', -⟩ := hC2 ρ hρ
    obtain ⟨x, hx, hxe⟩ := hcH ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩
    have hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv :=
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds hU
    have hmap : (lamConj M ρ (lamOf D cc δ)).map cj = lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ) := by
      apply hUI
      · rw [discr_map_cj, (hsp ρ).2.2, map_one]; exact one_ne_zero
      · rw [eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
      · rw [eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
    have hback : lamConj M ρ (lamOf D cc δ) = (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map cj := by
      rw [← hmap, map_cj_map_cj]
    refine ⟨(c ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩ : Ideal (𝓞 D.host.K)).map (conjO D), ?_, starRingEnd ℂ x,
      (map_ne_zero _).2 hx, by rw [hback, hxe, lamOf_map_cj]⟩
    intro hbot
    rw [Ideal.map_eq_bot_iff_of_injective (conjO D).injective] at hbot
    exact nonZeroDivisors.coe_ne_zero _ hbot

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem uniformization_holds : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization := by
  intro a b h
  refine ⟨?_, fun Λ Λ' hΛ hΛ' h2 h3 h2' h3' =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqLat_holds Λ Λ' hΛ hΛ' (h2.trans h2'.symm) (h3.trans h3'.symm)⟩
  obtain ⟨L, h2, h3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants h
  obtain ⟨e2, e3, hΔ, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  exact ⟨_, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds _ hΔ, e2.trans h2, e3.trans h3⟩

theorem conj_lattice_holds : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x :=
  conj_lattice uniformization_holds

end GlobalTheory.ConjLattice
end
end

