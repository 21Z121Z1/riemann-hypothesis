import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0263
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinorGroupMul
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal.JacAlg

def minorGroup {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) : AddSubgroup B :=
  AddSubgroup.closure {y | ∃ (b : A) (bs : Fin m → A),
    y = ρ b * (Matrix.of fun k l => D (κ k) (ρ (bs l))).det}

theorem minorGroup_mul {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) (a : A) {y : B}
    (hy : y ∈ minorGroup ρ D κ) : ρ a * y ∈ minorGroup ρ D κ := by
  unfold minorGroup at hy ⊢
  refine AddSubgroup.closure_induction (fun z hz => ?_) ?_
    (fun z₁ z₂ _ _ h₁ h₂ => ?_) (fun z _ hz => ?_) hy
  · obtain ⟨b, bs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a * b, bs, by rw [map_mul, mul_assoc]⟩
  · rw [mul_zero]
    exact zero_mem _
  · rw [mul_add]
    exact add_mem h₁ h₂
  · rw [mul_neg]
    exact neg_mem hz

theorem leibniz_pow {R : Type} [CommRing R] (q : R → R)
    (hmul : ∀ x y, q (x * y) = x * q y + y * q x) (φ : R) (N : ℕ) :
    q (φ ^ N) = (N : R) * φ ^ (N - 1) * q φ := by
  induction N with
  | zero =>
    have h1 := hmul 1 1
    simp only [mul_one, one_mul] at h1
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -h1
  | succ n ih =>
    rw [pow_succ, hmul, ih]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring

theorem column_clear {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw]
    (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A)
    (hc : μ.comp ι = lam.comp ρ) {d : ℕ} (D : Fin d → B → B) (p : Fin d → Bw → Bw)
    (hmul : ∀ k x y, p k (x * y) = x * p k y + y * p k x)
    (hD : ∀ k x, p k (lam x) = lam (D k x))
    (a : Af) (b : A) (N : ℕ) (hb : ι f ^ N * a = ι b) (k : Fin d) :
    lam (ρ (f ^ N) * D k (ρ b) + ρ (-(N : A) * f ^ (N - 1) * b) * D k (ρ f))
      = (lam (ρ f)) ^ (2 * N) * p k (μ a) := by
  have e1 : ∀ x, μ (ι x) = lam (ρ x) := fun x => by
    simpa using RingHom.congr_fun hc x
  have hF : lam (ρ f) ^ N * μ a = lam (ρ b) := by
    have h1 := congrArg μ hb
    rwa [map_mul, map_pow, e1, e1] at h1
  have hp1 := hmul k (lam (ρ f) ^ N) (μ a)
  rw [hF, hD, leibniz_pow (p k) (hmul k) (lam (ρ f)) N, hD] at hp1
  simp only [map_add, map_mul, map_neg, map_pow, map_natCast]
  rw [hp1, ← hF]
  ring

theorem det_mem {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) (f : A) {d m : ℕ}
    (D : Fin d → B → B) (κ : Fin m → Fin d) (c₁ c₂ b : Fin m → A) :
    (Matrix.of fun k l => ρ (c₁ l) * D (κ k) (ρ (b l))
      + ρ (c₂ l) * D (κ k) (ρ f)).det ∈ minorGroup ρ D κ := by
  classical
  unfold minorGroup
  set X : Fin m → Fin m → B := fun l k => ρ (c₁ l) * D (κ k) (ρ (b l)) with hX
  set Y : Fin m → Fin m → B := fun l k => ρ (c₂ l) * D (κ k) (ρ f) with hY
  have h1 : (Matrix.of fun k l => ρ (c₁ l) * D (κ k) (ρ (b l))
      + ρ (c₂ l) * D (κ k) (ρ f)).det = Matrix.det (Matrix.of fun l k => (X + Y) l k) := by
    rw [← Matrix.det_transpose]
    rfl
  have h2 : Matrix.det (Matrix.of fun l k => (X + Y) l k) =
      ∑ s : Finset (Fin m), Matrix.det (Matrix.of fun l k => s.piecewise X Y l k) :=
    (Matrix.detRowAlternating (n := Fin m) (R := B)).toMultilinearMap.map_add_univ X Y
  rw [h1, h2]
  refine AddSubgroup.sum_mem _ fun s _ => AddSubgroup.subset_closure ?_
  refine ⟨∏ l, (if l ∈ s then c₁ l else c₂ l), fun l => if l ∈ s then b l else f, ?_⟩
  rw [map_prod, ← Matrix.det_transpose (Matrix.of fun k l =>
      D (κ k) (ρ ((fun l => if l ∈ s then b l else f) l))),
    ← Matrix.det_mul_column]
  congr 1
  ext l k
  by_cases hl : l ∈ s <;> simp [hl, hX, hY, Finset.piecewise, Matrix.transpose_apply]

theorem det_clear {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw]
    (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A)
    (hc : μ.comp ι = lam.comp ρ) (hloc : ∀ a : Af, ∃ (b : A) (N : ℕ), ι f ^ N * a = ι b)
    {d m : ℕ} (D : Fin d → B → B) (p : Fin d → Bw → Bw)
    (hmul : ∀ k x y, p k (x * y) = x * p k y + y * p k x)
    (hD : ∀ k x, p k (lam x) = lam (D k x))
    (κ : Fin m → Fin d) (u : Fin m → Af) :
    ∃ (M : ℕ) (n : B), n ∈ minorGroup ρ D κ ∧
      (lam (ρ f)) ^ M * (Matrix.of fun k l => p (κ k) (μ (u l))).det = lam n := by
  classical
  choose bb NN hbN using hloc
  obtain ⟨N, hN⟩ : ∃ N, ∀ l, NN (u l) ≤ N :=
    ⟨Finset.univ.sup fun l => NN (u l), fun l => Finset.le_sup (f := fun l => NN (u l))
      (Finset.mem_univ l)⟩
  let b : Fin m → A := fun l => f ^ (N - NN (u l)) * bb (u l)
  have hb : ∀ l, ι f ^ N * u l = ι (b l) := by
    intro l
    simp only [b, map_mul, map_pow]
    rw [← hbN (u l), ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hN l)]
  have hcol : ∀ k l, lam (ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f))
      = lam (ρ f) ^ (2 * N) * p (κ k) (μ (u l)) :=
    fun k l => column_clear ρ lam ι μ f hc D p hmul hD (u l) (b l) N (hb l) (κ k)
  refine ⟨2 * N * m, (Matrix.of fun k l => ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f)).det,
    det_mem ρ f D κ (fun _ => f ^ N) (fun l => -(N : A) * f ^ (N - 1) * b l) b, ?_⟩
  rw [RingHom.map_det]
  have hmat : lam.mapMatrix (Matrix.of fun k l => ρ (f ^ N) * D (κ k) (ρ (b l))
      + ρ (-(N : A) * f ^ (N - 1) * b l) * D (κ k) (ρ f)) =
      Matrix.of fun k l => (fun _ => lam (ρ f) ^ (2 * N)) k * p (κ k) (μ (u l)) := by
    ext k l
    first
      | exact hcol k l
      | simpa using hcol k l
  rw [hmat, Matrix.det_mul_column, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul]
  rfl

theorem clear_sum : ∀ {A B Af Bw : Type} [CommRing A] [CommRing B] [CommRing Af] [CommRing Bw] (ρ : A →+* B) (lam : B →+* Bw) (ι : A →+* Af) (μ : Af →+* Bw) (f : A),
    μ.comp ι = lam.comp ρ → (∀ a : Af, ∃ (b : A) (N : ℕ), ι f ^ N * a = ι b) → (∀ x : B, lam x = 0 → ∃ N : ℕ, ρ f ^ N * x = 0) →
    ∀ {d m : ℕ} {Λ : Type} [Fintype Λ] (D : Fin d → B → B) (p : Fin d → Bw → Bw), (∀ k x y, p k (x + y) = p k x + p k y) →
      (∀ k x y, p k (x * y) = x * p k y + y * p k x) → (∀ k x, p k (lam x) = lam (D k x)) →
      ∀ (κ : Fin m → Fin d) (z : Λ → Af) (u : Λ → Fin m → Af) (x : B),
        lam x = ∑ L, μ (z L) * (Matrix.of fun k l => p (κ k) (μ (u L l))).det →
        ∃ M : ℕ, ρ f ^ M * x ∈ AddSubgroup.closure {y | ∃ (b : A) (bs : Fin m → A), y = ρ b * (Matrix.of fun k l => D (κ k) (ρ (bs l))).det} := by
  intro A B Af Bw _ _ _ _ ρ lam ι μ f hc hloc hker d m Λ _ D p _ hmul hD κ z u x hx
  classical
  have e1 : ∀ a : A, μ (ι a) = lam (ρ a) := fun a => by
    simpa using RingHom.congr_fun hc a
  choose MM nn hnn hMM using fun L => det_clear ρ lam ι μ f hc hloc D p hmul hD κ (u L)
  choose bz Nz hz using fun L => hloc (z L)
  obtain ⟨K, hK⟩ : ∃ K, ∀ L, MM L + Nz L ≤ K :=
    ⟨Finset.univ.sup fun L => MM L + Nz L, fun L => Finset.le_sup (f := fun L => MM L + Nz L)
      (Finset.mem_univ L)⟩
  let e : Λ → A := fun L => f ^ (K - (MM L + Nz L)) * bz L
  have hterm : ∀ L, lam (ρ f) ^ K * (μ (z L) * (Matrix.of fun k l => p (κ k) (μ (u L l))).det)
      = lam (ρ (e L) * nn L) := by
    intro L
    have hzL : lam (ρ f) ^ Nz L * μ (z L) = lam (ρ (bz L)) := by
      have h1 := congrArg μ (hz L)
      rwa [map_mul, map_pow, e1, e1] at h1
    have hK' : K = (K - (MM L + Nz L)) + Nz L + MM L := by
      have h := Nat.sub_add_cancel (hK L)
      rw [add_assoc, add_comm (Nz L) (MM L), h]
    simp only [e, map_mul, map_pow, ← hzL, ← hMM L]
    conv_lhs => rw [hK', pow_add, pow_add]
    ring
  have hymem : (∑ L, ρ (e L) * nn L) ∈ minorGroup ρ D κ :=
    AddSubgroup.sum_mem _ fun L _ => minorGroup_mul ρ D κ (e L) (hnn L)
  have h0 : lam (ρ f ^ K * x - ∑ L, ρ (e L) * nn L) = 0 := by
    rw [map_sub, map_mul, map_pow, hx, Finset.mul_sum, map_sum]
    simp only [hterm]
    exact sub_self _
  obtain ⟨N', hN'⟩ := hker _ h0
  refine ⟨N' + K, ?_⟩
  have h2 : ρ f ^ (N' + K) * x = ρ (f ^ N') * ∑ L, ρ (e L) * nn L := by
    rw [pow_add, mul_assoc, ← sub_eq_zero, map_pow, ← mul_sub]
    exact hN'
  rw [h2]
  exact minorGroup_mul ρ D κ (f ^ N') hymem

end GlobalTheory.CompanionTheory.ConeLocal.JacAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

variable {X Y : Scheme.{0}}

def chartFn {L : LB X} {d : ℤ} (s : LB.Sec (pw L d)) (i : L.ι) : Γ(X, L.U i) := s.f i

theorem map_prod_eq_pow_mul {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* B)
    (φ' : A' →+* B) {k : ℕ} (x : Fin k → A) (y : Fin k → A') (g : B)
    (h : ∀ l, φ (x l) = g * φ' (y l)) : φ (∏ l, x l) = g ^ k * φ' (∏ l, y l) := by
  rw [map_prod, map_prod, Finset.prod_congr rfl (fun l _ => h l), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def secMono {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d))
    (w : Fin k → τ) : LB.Sec (pw L D) where
  f i := ∏ l, chartFn (a (w l)) i
  compat i j := by
    subst h
    have := map_prod_eq_pow_mul (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom
      (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom
      (fun l => chartFn (a (w l)) i) (fun l => chartFn (a (w l)) j)
      ((L.g i j ^ d : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) (fun l => (a (w l)).compat i j)
    refine this.trans ?_
    congr 1
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
    rfl

def pullPow {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) (t : ℤ) :
    LB.Iso (pw N t) ((pw N' t).pull β) :=
  ⟨fun p => v.s p ^ t⟩

theorem prod_mul_prod_eq {B τ : Type} [CommMonoid B] (φ : τ → B) {k : ℕ} (w₁ w₂ w₃ w₄ : Fin k → τ)
    (hw : Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) :
    (∏ l, φ (w₁ l)) * ∏ l, φ (w₂ l) = (∏ l, φ (w₃ l)) * ∏ l, φ (w₄ l) := by
  have key : ∀ w : Fin k → τ, ∏ l, φ (w l) = ((Finset.univ.val.map w).map φ).prod := by
    intro w
    rw [Multiset.map_map]
    rfl
  rw [key, key, key, key, ← Multiset.prod_add, ← Multiset.prod_add, ← Multiset.map_add, ← Multiset.map_add, hw]

theorem secMono_mul : ∀ {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d)) (w₁ w₂ w₃ w₄ : Fin k → τ), (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (secMono h a w₁).f c * (secMono h a w₂).f c = (secMono h a w₃).f c * (secMono h a w₄).f c := by
  intro X L τ d D k h a w₁ w₂ w₃ w₄ hw c
  exact prod_mul_prod_eq (fun i => chartFn (a i) (show L.ι from c)) w₁ w₂ w₃ w₄ hw

theorem zpow_mul_inv_eq {G : Type} [CommGroup G] (a a' b b' : G) (t : ℤ) (h : a' = a ^ t) (h' : b' = b ^ t) :
    (a * b⁻¹) ^ t = a' * b'⁻¹ := by
  rw [h, h', mul_zpow, inv_zpow]

theorem mapmap_zpow {G H K : Type} [CommGroup G] [CommGroup H] [CommGroup K] (f : G →* H) (g : H →* K)
    (x : G) (t : ℤ) : g (f (x ^ t)) = (g (f x)) ^ t := by
  rw [map_zpow, map_zpow]

theorem pull_pw_g {Z W : Scheme.{0}} (L : LB W) (φ : Z ⟶ W) (t : ℤ) (i j : PUnit → L.ι) :
    ((pw L t).pull φ).g i j = ((L.pull φ).g i j) ^ t := by
  refine (pull_g (pw L t) φ i j).trans ((mapmap_zpow (pullU φ _) (res _) (L.g _ _) t).trans ?_)
  exact congrArg (· ^ t) (pull_g L φ i j).symm

theorem pullPow_isGen : ∀ {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) (t : ℤ), v.IsGen → (pullPow v t).IsGen := by
  intro X Y N N' β v t hv p q
  have := congrArg (· ^ t) (hv p q)
  simp only [mul_zpow, ← map_zpow] at this
  refine this.trans ?_
  congr 1
  refine zpow_mul_inv_eq (G := Γ(X, (N'.pull β).U p.1 ⊓ N.U p.2 ⊓ ((N'.pull β).U q.1 ⊓ N.U q.2))ˣ)
    (res _ ((N'.pull β).g p.1 q.1)) (res _ (((pw N' t).pull β).g p.1 q.1)) (res _ (N.g p.2 q.2))
    (res _ ((pw N t).g p.2 q.2)) t ?_ ?_
  · exact (congrArg _ (pull_pw_g N' β t p.1 q.1)).trans (map_zpow _ _ _)
  · exact map_zpow _ _ _

theorem secMaps_secMono : ∀ {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw N d)) (a' : τ → LB.Sec (pw N' d)), (∀ i, SecMaps (pullPow v d) (a i) (secPull (a' i) β)) → ∀ w : Fin k → τ, SecMaps (pullPow v D) (secMono h a w) (secPull (secMono h a' w) β) := by
  intro X Y N N' β v τ d D k h a a' hmaps w p
  subst h
  let u : Γ(X, (N'.pull β).U p.1 ⊓ N.U p.2)ˣ := v.s p
  refine (map_prod_eq_pow_mul
    ((resG X (inf_le_left)).comp ((resG X (GlobalTheory.Cartier.pull_U N' β p.1).le).comp (β.app _).hom))
    (resG X inf_le_right) (fun l => chartFn (a' (w l)) (p.1 ⟨⟩)) (fun l => chartFn (a (w l)) p.2)
    (u ^ d).val (fun l => hmaps (w l) p)).trans ?_
  congr 1
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
  rfl

theorem nonzeroLocus_secMono_const : ∀ {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d)) (i : τ), 1 ≤ k → nonzeroLocus (secMono h a (fun _ => i)) = nonzeroLocus (a i) := by
  intro X L τ d D k h a i hk
  refine iSup_congr fun c => ?_
  change X.basicOpen (∏ l : Fin k, chartFn (a i) c) = X.basicOpen (chartFn (a i) c)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact Scheme.basicOpen_pow _ _ (by omega)

end GlobalTheory.CompanionTheory.FormalAlg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneGeneratedOfField
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.NormOneField

open Polynomial in

theorem normOneGen_of_imag {R : Type} [CommRing R] [IsDomain R] [CharZero R]
    (hinv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) (c : R →+* R) (θ : R) (hθ : θ ≠ 0) (hc : c θ = -θ) :
    NormOneGen c := by
  have hU : ∀ a : R, a ≠ 0 → IsUnit a := fun a ha => by
    obtain ⟨b, hb⟩ := hinv a ha
    exact isUnit_iff_exists_inv.2 ⟨b, hb⟩
  intro α p hα _
  by_cases hp : p = 0
  · subst hp
    refine ⟨1, by simp, by simpa using hα, ?_⟩
    simpa using (hU 2 two_ne_zero).mul hα
  have hne : ∀ n : ℕ, (n : R) - θ ≠ 0 := by
    intro n h
    have e : θ = n := (sub_eq_zero.1 h).symm
    have h1 : c θ = θ := by
      rw [e, map_natCast]
    have h2 : (2 : R) * θ = 0 := by linear_combination hc - h1
    exact hθ ((mul_eq_zero.1 h2).resolve_left two_ne_zero)
  choose i hi using fun n : ℕ => hinv _ (hne n)
  set m : ℕ → R := fun n => ((n : R) + θ) * i n with hm
  have hnorm : ∀ n, m n * c (m n) = 1 := by
    intro n
    have h1 : c (((n : R) - θ) * i n) = 1 := by rw [hi, map_one]
    rw [map_mul, map_sub, map_natCast, hc] at h1
    simp only [hm, map_mul, map_add, map_natCast, hc]
    linear_combination (((n : R) - -θ) * c (i n)) * hi n + h1
  have hminj : Function.Injective m := by
    intro a b h
    have h' : ((a : R) + θ) * i a = ((b : R) + θ) * i b := h
    have h1 : ((a : R) + θ) * ((b : R) - θ) = ((b : R) + θ) * ((a : R) - θ) := by
      linear_combination ((a : R) - θ) * ((b : R) - θ) * h' - ((a : R) + θ) * ((b : R) - θ) * hi a +
        ((b : R) + θ) * ((a : R) - θ) * hi b
    have h2 : ((2 : R) * ((b : R) - a)) * θ = 0 := by linear_combination h1
    have h3 : (b : R) - a = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hθ)).resolve_left two_ne_zero
    exact (Nat.cast_injective (R := R) (sub_eq_zero.1 h3)).symm
  set q : R[X] := X ^ 2 - C (2 * α) * X + C (p * c p) with hq
  have hq0 : q ≠ 0 := by
    intro h
    have h2 := congrArg (fun r => r.coeff 2) h
    simp [hq, coeff_X, coeff_C] at h2
  have hY : ({α} ∪ {y | q.IsRoot y} : Set R).Finite :=
    (Set.finite_singleton α).union (Polynomial.finite_setOf_isRoot hq0)
  have hg : Function.Injective (fun n => m n * p) := fun a b h =>
    hminj (mul_right_cancel₀ hp h)
  obtain ⟨n, hn⟩ := (hY.preimage hg.injOn).exists_notMem
  refine ⟨m n, hnorm n, hU _ fun h => hn (Or.inl (sub_eq_zero.1 h).symm), hU _ fun h => hn (Or.inr ?_)⟩
  rw [map_mul] at h
  have h4 := hnorm n
  change q.IsRoot (m n * p)
  simp only [hq, IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  linear_combination (-(m n * p)) * h - (p * c p) * h4

theorem exists_imag {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hw : w.IsComplex := hcm.2.1.isComplex w
  have hτ : ¬ ComplexEmbedding.IsReal w.embedding := InfinitePlace.isComplex_iff.1 hw
  have hx : ∃ x : E, σ x ≠ x := by
    by_contra h
    push Not at h
    apply hτ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hcm.2.2.2 w.embedding x
    rw [h x] at this
    exact this.symm
  obtain ⟨x, hx⟩ := hx
  have hσσ : σ (σ x) = x := w.embedding.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  exact ⟨x - σ x, sub_ne_zero.2 hx.symm, by rw [map_sub, hσσ, neg_sub]⟩

theorem normOne_of_isField : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) →
    NormOneGen (sigR K σ) := by
  intro F E _ _ _ _ _ σ hCM K _ _ hf
  haveI : Nontrivial (K ⊗[F] E) := ⟨hf.exists_pair_ne⟩
  haveI : IsDomain (K ⊗[F] E) := hf.isDomain
  haveI : CharZero (K ⊗[F] E) :=
    charZero_of_injective_algebraMap (R := F) (algebraMap F (K ⊗[F] E)).injective
  obtain ⟨δ, hδ, hσδ⟩ := exists_imag hCM
  have hs : sigR K σ (inclR K δ) = inclR K (σ δ) := by
    simp [sigR, inclR]
  refine normOneGen_of_imag (fun a ha => hf.mul_inv_cancel ha) (sigR K σ) (inclR K δ) ?_ ?_
  · intro h
    have h1 : inclR (F := F) K (δ * δ⁻¹) = 0 := by rw [map_mul, h, zero_mul]
    rw [mul_inv_cancel₀ hδ, map_one] at h1
    exact one_ne_zero h1
  · rw [hs, hσδ, map_neg]

end GlobalTheory.CompanionTheory.SaGen.NormOneField
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalBasisBaseChange
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem isCMExt_sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (t : E) : σ (σ t) = t := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem hform_incV {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (K : Type) [CommRing K] [Algebra F K] (x y : Fin M → E) :
    Formalism.UG.hform (sigR K σ) (JR K J) (incV K x) (incV K y) = inclR K (hf σ J x y) := by
  simp only [Formalism.UG.hform, hf, incV, JR, map_sum, map_mul, Matrix.map_apply]
  rfl

theorem exists_rational_orth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (K : Type) [Field K] [Algebra F K], ∃ e : Fin M → Fin M → K ⊗[F] E,
      (∀ i j, i ≠ j → Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e j) = 0) ∧
      (∀ i, IsUnit (Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e i))) ∧ IsUnit (Matrix.of e).det := by
  intro F E _ _ _ _ _ σ hσ M J hJ K _ _
  have hcc := isCMExt_sigma_sigma hσ
  obtain ⟨P, d, hP, hd, -, hd0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) (G := J)
    two_ne_zero hcc (fun a b => hJ.1 b a)
  have hd0' := hd0 hJ.2
  let x : Fin M → Fin M → E := fun i k => σ (P k i)
  have hx : ∀ i j, hf σ J (x i) (x j) = (Matrix.diagonal d) i j := by
    intro i j
    rw [← hd]
    simp only [hf, x, hcc, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  refine ⟨fun i => incV K (x i), fun i j hij => ?_, fun i => ?_, ?_⟩
  · rw [hform_incV, hx, Matrix.diagonal_apply_ne _ hij, map_zero]
  · rw [hform_incV, hx, Matrix.diagonal_apply_eq]
    exact (IsUnit.mk0 _ (hd0' i)).map _
  · have hm : Matrix.of (fun i => incV (F := F) K (x i)) = ((P.map σ).transpose).map (inclR K) := by
      ext i k
      rfl
    rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose]
    have : (P.map σ).det = σ P.det := (RingHom.map_det (σ : E →+* E) P).symm
    rw [this]
    exact (IsUnit.mk0 _ ((map_ne_zero σ).2 hP)).map _

end GlobalTheory.CompanionTheory.SaGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodProductFiltrationLevels
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem prod_eq_t_mul_unit_count : ∀ {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (t : ι → Formalism.Per6.BdRp l) (i₀ : ι), i₀ ∈ s →
    ∀ u : (Formalism.Per6.BdRp l)ˣ, ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l * (u : Formalism.Per6.BdRp l) →
      thB l (t i₀) = 0 →
      ∀ μ ∈ s, (μ = i₀ → t μ ∉ FB l 2) ∧ (μ ≠ i₀ → t μ ∉ FB l 1) := by
  intro l _ ι s t i₀ hi₀ u hprod h0 μ hμ
  have hmax : IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) = Ideal.span {GroundTheory.PAdicHodge.tBdR l} :=
    GroundTheory.PAdicHodge.maximalIdeal_eq_span_fontaineT GroundTheory.PAdicHodge.untilt_epsilon
      GroundTheory.PAdicHodge.untilt_frobeniusEquiv_symm_epsilon_ne_one
  have htirr : Irreducible (GroundTheory.PAdicHodge.tBdR l) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2 hmax
  have hFB : ∀ k, FB l k = Ideal.span {GroundTheory.PAdicHodge.tBdR l ^ k} := fun k => by
    rw [FB, ker_thB_eq, hmax, Ideal.span_singleton_pow]
  have hnot : ¬ (GroundTheory.PAdicHodge.tBdR l ^ 2 ∣ ∏ μ ∈ s, t μ) := by
    rw [hprod, pow_two]
    intro h
    have h1 : GroundTheory.PAdicHodge.tBdR l ∣ (u : Formalism.Per6.BdRp l) :=
      (mul_dvd_mul_iff_left htirr.ne_zero).1 h
    exact htirr.not_isUnit (isUnit_of_dvd_unit h1 u.isUnit)
  have hi : GroundTheory.PAdicHodge.tBdR l ∣ t i₀ := by
    have : t i₀ ∈ FB l 1 := by
      rw [FB, pow_one, RingHom.mem_ker]; exact h0
    rw [hFB, pow_one] at this
    exact Ideal.mem_span_singleton.1 this
  refine ⟨fun e hm => hnot ?_, fun hne hm => hnot ?_⟩
  · subst e
    rw [hFB] at hm
    exact (Ideal.mem_span_singleton.1 hm).trans (Finset.dvd_prod_of_mem t hμ)
  · rw [hFB, pow_one] at hm
    have hd := Ideal.mem_span_singleton.1 hm
    have hμ' : μ ∈ s.erase i₀ := Finset.mem_erase.2 ⟨hne, hμ⟩
    rw [← Finset.mul_prod_erase s t hi₀, ← Finset.mul_prod_erase (s.erase i₀) t hμ', pow_two, ← mul_assoc]
    exact (mul_dvd_mul hi hd).mul_right _

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperInfIdealSheavesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_inf_ideal_sheaves : ∀ {X S : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] (T₁ T₂ : X.IdealSheafData), IsProper (T₁.subschemeι ≫ f) → IsProper (T₂.subschemeι ≫ f) → IsProper ((T₁ ⊓ T₂).subschemeι ≫ f) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Union.isProper_inf | exact GlobalTheory.CompanionTheory.GE.Union.isProper_inf | (intros; apply GlobalTheory.CompanionTheory.GE.Union.isProper_inf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subobject_le_iff_affine_sections : ∀ {X : Scheme.{0}} {E : X.Modules} (S T : Subobject E), S ≤ T ↔ ∀ U : X.affineOpens, secs S (U : X.Opens) ⊆ secs T (U : X.Opens) := by
  first | exact @GlobalTheory.CompanionTheory.GE.le_iff_secs_subset | exact GlobalTheory.CompanionTheory.GE.le_iff_secs_subset | (intros; apply GlobalTheory.CompanionTheory.GE.le_iff_secs_subset <;> assumption)
end

