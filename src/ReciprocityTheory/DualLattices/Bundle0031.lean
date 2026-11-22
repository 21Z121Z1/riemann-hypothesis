import ReciprocityTheory.DualLattices.Bundle0029
import ReciprocityTheory.DualLattices.Bundle0022
import ReciprocityTheory.DualLattices.UnramifiedCokernelLengthOfLengthEigenLengthProduct
import ReciprocityTheory.DualLattices.Bundle0001
import ReciprocityTheory.DualLattices.Bundle0030
import ReciprocityTheory.DualLattices.SubMemOfCompat

-- bundled from ReciprocityTheory.DualLattices.CharR
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

lemma ATower.char_R {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : ((p ^ (n + 1) : ℕ) : (Tw.R n : Type u)) = 0 := by
  have h := congrArg (Tw.π n).1 (Tw.char n)
  rwa [map_natCast, map_zero] at h

theorem lim (B : BX R₀) (hB1 : PairingPropertiesStatement B) {p : ℕ} (Tw : ATowerL R₀ p) (Dt : DualTower Tw) :
    LimStatement B Tw Dt := by
  intro ι τ hτ hc
  have hN : ∀ n, ((p ^ (n + 1) : ℕ) : (Tw.R n : Type u)) = 0 := fun n => Tw.toATower.char_R n
  have hy : ∀ i n, (p ^ (n + 1)) • B.map (Tw.q n) (τ i n) = 0 := fun i n => by
    rw [← map_nsmul, hτ i n, map_zero]
  have hex : ∀ i n, ∃ h, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n)) h :=
    fun i n => BX.isHeight_exists (B := B) hB1 (Dt.Dp n) _ (hN n) _ (hy i n)
  choose h hh using hex
  have hcomp : ∀ i n, (Tw.r n).1.toLinearMap ∘ₗ h i (n + 1) = h i n := by
    intro i n
    have H1 := BX.isHeight_map (B := B) hB1 (Dt.Dp (n + 1)) (Dt.Dp n) (Tw.r n) (Dt.d n) (Dt.d_π n)
      (Dt.d_σ n) (Dt.d_η n) _ _ _ (hh i (n + 1))
    rw [← B.map_comp, BX.tw_qr Tw n, pow_succ] at H1
    have hy1 : (p ^ (n + 1) * p) • B.map (Tw.q n) (τ i (n + 1)) = 0 := by
      rw [← pow_succ, ← map_nsmul, hτ i (n + 1), map_zero]
    have H2 := BX.isHeight_mul_p (B := B) hB1 (Dt.Dp n) (p ^ (n + 1)) p (hN n) _ hy1 _ H1
    rw [← map_nsmul, ← hc i n] at H2
    exact BX.isHeight_unique (B := B) hB1 (Dt.Dp n) _ (hN n) _ (hy i n) _ _ H2 (hh i n)
  have hlimv : ∀ i (v : B.gg), ∃ a : (Tw.O : Type u), ∀ n, (Tw.q n).1 a = h i n v := fun i v =>
    Tw.complete (fun n => h i n v) (fun n => by
      have := LinearMap.congr_fun (hcomp i n) v
      simpa using this)
  choose hta hta_spec using hlimv
  have hsep : ∀ a b : (Tw.O : Type u), (∀ n, (Tw.q n).1 a = (Tw.q n).1 b) → a = b := fun a b hab =>
    sub_eq_zero.mp (Tw.sep _ (fun n => by rw [map_sub, hab n, sub_self]))
  let ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u) := fun i =>
    { toFun := hta i
      map_add' := fun v w => hsep _ _ (fun n => by simp only [map_add, hta_spec])
      map_smul' := fun c v => hsep _ _ (fun n => by simp only [map_smul, hta_spec, RingHom.id_apply]) }
  have hlift : ∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) :=
    fun i n => BX.exists_lift (B := B) Tw.toATower n _ (hy i n)
  choose th w hthw using hlift
  have hwb : ∀ i n, LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap
      (LinearMap.lTensor B.gg (Tw.π (n + 1)).1.toLinearMap (w i (n + 1))) =
      LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n) := by
    intro i n
    obtain ⟨d1, d2, d3⟩ := BX.lift_down (B := B) Tw n (τ i (n + 1)) (th i (n + 1)) (w i (n + 1))
      (hthw i (n + 1)).1 (hthw i (n + 1)).2
    rw [← d3]
    apply BX.lift_indep (B := B) Tw.toATower n _ _ _ _ ?_ d2 (hthw i n).2
    rw [d1, ← hc i n, (hthw i n).1]
  have hbt : ∀ i, ∃ bt : B.gg ⊗[R₀] (Tw.O : Type u), ∀ n,
      LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap bt =
        LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n) := fun i =>
    BX.exists_lim_tensor (B := B) Tw (fun n => LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (w i n))
      (hwb i)
  choose bt hbt using hbt
  refine ⟨ht, bt, fun i n => ?_, fun i n => ⟨th i n, w i n, (hthw i n).1, (hthw i n).2, (hbt i n).symm⟩⟩
  have hq : (Tw.q n).1.toLinearMap ∘ₗ ht i = h i n := by
    ext v
    simp [ht, hta_spec]
  rw [hq]
  exact hh i n

theorem htLin (B : BX R₀) (hB1 : PairingPropertiesStatement B) {p : ℕ} (Tw : ATower R₀ p) (Dp : ∀ n, DualPair (Tw.R n)) :
    HtLinStatement B Tw Dp := by
  intro ι _ τ ht a α hτ hH hα n
  have hN := Tw.char_R n
  have hy : ∀ i, (p ^ (n + 1)) • B.map (Tw.q n) (τ i n) = 0 := fun i => by
    rw [← map_nsmul, hτ i n, map_zero]
  have hlin : (Tw.q n).1.toLinearMap ∘ₗ ∑ i, α i • ht i =
      ∑ i, a i n • ((Tw.q n).1.toLinearMap ∘ₗ ht i) := by
    ext v
    simp [LinearMap.sum_apply, map_sum, map_mul, hα, zsmul_eq_mul]
  rw [map_sum, hlin]
  simp only [map_zsmul]
  exact BX.isHeight_sum (B := B) hB1 (Dp n) (p ^ (n + 1)) hN Finset.univ
    (fun i => a i n • B.map (Tw.q n) (τ i n)) (fun i => by rw [smul_comm, hy i, smul_zero])
    (fun i => a i n • ((Tw.q n).1.toLinearMap ∘ₗ ht i))
    (fun i => BX.isHeight_zsmul (B := B) hB1 (Dp n) (p ^ (n + 1)) hN (hy i) (hH i n) (a i n))

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.ExistsReductionOfCoordinateCombination
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Lift

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def nbAct (H : HodgeTateDatum p g v R O σ cp) (a : O) (y : Nb p g) : Nb p g :=
  (H.ρ a).map PadicInt.toZMod *ᵥ y

lemma red_mulVec (H : HodgeTateDatum p g v R O σ cp) (a : O) (t : TT p g) :
    red p g (H.ρ a *ᵥ t) = nbAct H a (red p g t) := by
  funext i
  exact RingHom.map_mulVec PadicInt.toZMod (H.ρ a) t i

lemma red_surj (y : Nb p g) : ∃ t : TT p g, red p g t = y := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ⟨fun i => ((y i).val : ℤ_[p]), funext fun i => by
    show PadicInt.toZMod (((y i).val : ℕ) : ℤ_[p]) = y i
    rw [map_natCast, ZMod.natCast_zmod_val]⟩

lemma comp_mem (H : HodgeTateDatum p g v R O σ cp) (a : O) {f : Nb p g → C} (hf : f ∈ H.AA.carrier) :
    (fun y => f (nbAct H a y)) ∈ H.AA.carrier := by
  obtain ⟨f', hf', hf'e⟩ := H.h3 a f hf
  have hfun : (fun y => f (nbAct H a y)) = f' := by
    funext y
    obtain ⟨t, rfl⟩ := red_surj y
    rw [hf'e, red_mulVec]
  rw [hfun]
  exact hf'

variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)

private lemma smul_cancel_lemma {S K : Type*} [CommRing S] [Field K] [Algebra S K]
    (hinj : Function.Injective (algebraMap S K)) {ι κ : Type*} {M : Matrix ι κ S} (hM : M ≠ 0)
    {a b : S} (h : a • M = b • M) : a = b := by
  obtain ⟨x, y, hxy⟩ : ∃ x y, M x y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hM (Matrix.ext fun x y => by simpa using hc x y)
  have h2 : a * M x y = b * M x y := by
    have := congrFun (congrFun h x) y
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  have h3 : algebraMap S K (a - b) * algebraMap S K (M x y) = 0 := by
    rw [← map_mul, sub_mul, h2, sub_self, map_zero]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp (hinj (by rw [h4, map_zero]))
  · exact absurd (hinj (by rw [h4, map_zero])) hxy

end Lift

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.FrobeniusBlock
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix ReciprocityTheory.PGsh.Up.UnitVectorPowers

theorem frobeniusBlock : FrobeniusBlockStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp _ hS H U X D
  have hv := hS.integers
  have hp1 := hS.p_lt
  haveI := isLocal_of_integers hv
  haveI : CharP (IsLocalRing.ResidueField R) p := by
    have h0 := residue_p hv hp1
    first
      | exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0
      | exact CharP.of_prime_eq_zero Fact.out h0
      | exact (charP_iff_prime_eq_zero Fact.out).mpr h0
  refine ⟨fun j l hl => ?_, fun i e => ?_⟩
  · rw [linX_xp hv hp1 D j l, bR_off hv hp1 D j l hl, map_zero, zero_mul]
  ·
    have hM : (Matrix.of fun j l : {j // D.κ j = i} =>
        linX D (fun y => xL D j.1 y ^ p) (e l).1) =
        Matrix.of fun j l : {j // D.κ j = i} =>
          algebraMap R C (bR hv D j.1 (e1 (e l).1)) *
            (algebraMap R C (D.ε j.1) ^ p / algebraMap R C (D.ε (e l).1)) := by
      ext j l
      simp only [Matrix.of_apply]
      exact linX_xp hv hp1 D j.1 (e l).1
    have hs := Det2.v_det_scaled v
      (Matrix.of fun j l : {j // D.κ j = i} => algebraMap R C (bR hv D j.1 (e1 (e l).1)))
      (fun j => algebraMap R C (D.ε j.1) ^ p) (fun l => algebraMap R C (D.ε (e l).1))
    simp only [Matrix.of_apply] at hs

    have hcB : (Matrix.of fun j l : {j // D.κ j = i} =>
        algebraMap R C (bR hv D j.1 (e1 (e l).1))).det =
        algebraMap R C (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det := by
      rw [RingHom.map_det]
      first
        | rfl
        | (congr 1; ext j l; simp [RingHom.mapMatrix_apply])
    have hres : IsLocalRing.residue R
        (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det =
        (Matrix.of fun j l : {j // D.κ j = i} => Mk D j.1 (e l).1).det := by
      rw [RingHom.map_det]
      congr 1
      ext j l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      exact res_bR hv hp1 D _ _
    have hunit : IsUnit
        (Matrix.of fun j l : {j // D.κ j = i} => bR hv D j.1 (e1 (e l).1)).det := by
      by_contra h
      apply block_det_ne hv hp1 D i e
      rw [← hres, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact h
    have h1 := hv.one_of_isUnit hunit
    have hy : ∏ j : {j // D.κ j = i}, v (algebraMap R C (D.ε j.1) ^ p) = X i ^ p := by
      rw [← D.ε_prod i, ← Finset.prod_pow]
      simp only [map_pow]
      exact (Finset.prod_subtype _ (fun j => by simp)
        (fun j => v (algebraMap R C (D.ε j)) ^ p)).symm
    have hz : ∏ k : {j // D.κ j = i}, v (algebraMap R C (D.ε (e k).1)) = X (U.φ i) :=
      (Equiv.prod_comp e (fun l : {l // D.κ l = U.φ i} => v (algebraMap R C (D.ε l.1)))).trans
        ((Finset.prod_subtype _ (fun l => by simp)
          (fun l => v (algebraMap R C (D.ε l)))).symm.trans (D.ε_prod (U.φ i)))
    rw [hM, hs, hcB, h1, hy, hz, one_mul]

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.HtdOf
section
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def Dat.hopf (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C] [Algebra (Tw.O : Type) C]
    (hdom : IsDomain (Tw.O : Type)) (hinj : Function.Injective (algebraMap (Tw.O : Type) C))
    (hLat : EvLatStatement D) (hHopf : EvHopfStatement D) : HopfOrder (C := C) (Tw.O : Type) (Nb p g) where
  carrier := D.evImg C
  lat := (hLat C hdom hinj).1
  le_int := (hLat C hdom hinj).2.1
  one_mem := (hLat C hdom hinj).2.2.1
  mul_mem := (hLat C hdom hinj).2.2.2
  comul := (hHopf C hinj).1
  antipode := (hHopf C hinj).2

def htd_of (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C] (v : Valuation C NNReal)
    [Algebra (Tw.O : Type) C] (hdom : IsDomain (Tw.O : Type))
    (hinj : Function.Injective (algebraMap (Tw.O : Type) C))
    (hLat : EvLatStatement D) (hHopf : EvHopfStatement D) (hAct : EvActStatement D)
    (hHt : EvHtStatement D) (hBt : EvBtStatement D) (hH5 : EvenTwoEvaluationSign D) (hCot : EvCotStatement D) :
    HodgeTateDatum p g v (Tw.O : Type) Oe σ cp where
  ρ := D.H.ρ
  ρL := D.H.ρL
  P := D.H.P
  PL := D.H.PL
  E := D.H.E
  E_alternating := D.H.E_alternating
  isUnit_det_E := D.H.isUnit_det_E
  E_equivariant := D.H.E_equivariant
  projectors := D.H.projectors
  Ht := D.H.Ht
  Bt := D.H.Bt
  Ht_equivariant := D.H.Ht_equivariant
  form_eq_alt := D.H.form_eq_alt
  AA := D.hopf C hdom hinj hLat hHopf
  h3 := fun a f hf => hAct C a f hf
  h4 := fun k => ⟨hHt C k, hBt C k⟩
  h5 := fun hp2 s => hH5 C hdom hinj hp2 s
  φ := Classical.choose (hCot C hinj)
  cotangent_surjective := (Classical.choose_spec (hCot C hinj)).1
  cotangent_ker_eq := (Classical.choose_spec (hCot C hinj)).2.1
  cotangent_linear := (Classical.choose_spec (hCot C hinj)).2.2

end ReciprocityTheory.PGsh.Be2
end
end

-- bundled from ReciprocityTheory.DualLattices.MulVecMemPP
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section F3b

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

def sumX (D : Lifts H U X) : (Ix g → R) →ₗ[R] augIdeal H.AA.carrier where
  toFun c := ⟨∑ k, c k • xL D k, Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (D.x_mem k)⟩
  map_add' c c' := by apply Subtype.ext; simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by apply Subtype.ext; simp [Finset.smul_sum, smul_smul]

omit [Fact p.Prime] in
lemma mem_pP {n : ℕ} (w : Fin n → R) :
    w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R)) ↔ ∃ w', w = (p : R) • w' := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w', _, hw'⟩
    exact ⟨w', hw'.symm⟩
  · rintro ⟨w', hw'⟩
    exact ⟨w', Submodule.mem_top, hw'.symm⟩

omit [Fact p.Prime] in
lemma mulVec_mem_pP {n n' : ℕ} (M : Matrix (Fin n') (Fin n) R) {w : Fin n → R}
    (hw : w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R))) :
    M *ᵥ w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n' → R)) := by
  obtain ⟨w', rfl⟩ := (mem_pP w).1 hw
  exact (mem_pP _).2 ⟨M *ᵥ w', Matrix.mulVec_smul M (p : R) w'⟩

lemma εL_eq_zero_of_r (U : UnramData p g v R O σ cp H) {τ : Fin U.m} (h : U.r τ = 0) :
    U.εL τ = 0 := by
  obtain ⟨e⟩ := U.rank τ
  haveI : Subsingleton (Fin (U.r τ) → R) := by rw [h]; infer_instance
  haveI : Subsingleton (LinearMap.range (Matrix.mulVecLin (U.εL τ))) := e.toEquiv.subsingleton
  ext i j
  have h1 : (⟨U.εL τ *ᵥ Pi.single j 1, LinearMap.mem_range_self _ _⟩ :
      LinearMap.range (Matrix.mulVecLin (U.εL τ))) = 0 := Subsingleton.elim _ _
  have h2 := congrArg (fun x : LinearMap.range (Matrix.mulVecLin (U.εL τ)) => (x : Fin g → R) i) h1
  simpa [Matrix.mulVec_single_one] using h2

lemma phi_x_grade (hS : HodgeTateSetting p v R O σ cp) (D : Lifts H U X) (k : Ix g) (τ : Fin U.m)
    (hτ : τ ≠ D.κ k) (l : Fin g → R)
    (hl : H.φ ⟨xL D k, D.x_mem k⟩ = Submodule.Quotient.mk l) :
    (U.εL τ)ᵀ *ᵥ l ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin g → R)) := by
  by_cases hτκ : ∃ j, D.κ j = τ
  · obtain ⟨j', rfl⟩ := hτκ
    obtain ⟨k', hk'⟩ := D.sep j' k hτ
    have hf' : ∀ t, ((U.sg (D.κ k) (D.b k') • (⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) :
        augIdeal H.AA.carrier) : Nb p g → C) (red p g t) =
        ((⟨xL D k, D.x_mem k⟩ : augIdeal H.AA.carrier) : Nb p g → C) (red p g (H.ρ (D.b k') *ᵥ t)) := by
      intro t
      simp only [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, xL]
      rw [D.eig k k' t]
      ring
    have h1 := H.cotangent_linear (D.b k') _ _ l hf' hl
    rw [map_smul, hl, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h1
    have h2 := mulVec_mem_pP (U.εL (D.κ j'))ᵀ h1
    have e : (U.εL (D.κ j'))ᵀ *ᵥ (U.sg (D.κ k) (D.b k') • l - (H.ρL (D.b k'))ᵀ *ᵥ l) =
        (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k')) • ((U.εL (D.κ j'))ᵀ *ᵥ l) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, U.εL_eig,
        Matrix.transpose_smul, Matrix.smul_mulVec, sub_smul]
    rw [e] at h2
    have hv : v (algebraMap R C (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k'))) = 1 := by
      rw [← neg_sub, map_neg, Valuation.map_neg]
      exact hk'
    have hunit : IsUnit (U.sg (D.κ k) (D.b k') - U.sg (D.κ j') (D.b k')) := by
      refine hS.integers.isUnit_of_one ?_ hv
      exact Ne.isUnit fun h0 => by rw [h0, Valuation.map_zero] at hv; exact zero_ne_one hv
    obtain ⟨u, hu⟩ := hunit
    have h3 := Submodule.smul_mem _ (↑u⁻¹ : R) h2
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h3
  · push_neg at hτκ
    rw [εL_eq_zero_of_r U (D.r_zero τ hτκ), Matrix.transpose_zero, Matrix.zero_mulVec]
    exact Submodule.zero_mem _

end F3b

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.SurjectiveAinfTowerZero
section
noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)

theorem surjective_ainfTower_zero : Function.Surjective ((ainfTowerL p O hv ε hε).q 0).1 :=
  fun y => Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O) ^ (0 + 1)}) y

theorem ker_ainfTower_zero : RingHom.ker ((ainfTowerL p O hv ε hε).q 0).1 =
    Ideal.span {((p : ℕ) : ((ainfTowerL p O hv ε hε).O : Type))} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  have hq : ((ainfTowerL p O hv ε hε).q 0).1 a =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ (0 + 1)}) a := rfl
  rw [hq]
  exact (Ideal.Quotient.eq_zero_iff_dvd _ _).trans (by rw [pow_one]; rfl)

theorem ainf_zeta0 (h2 : p = 2) :
    (((ainfTowerL p O hv ε hε).ζ 0 : ((ainfTowerL p O hv ε hε).O : Type)ˣ) :
      ((ainfTowerL p O hv ε hε).O : Type)) = -1 := by
  have hz : (((ainfTowerL p O hv ε hε).ζ 0 : ((ainfTowerL p O hv ε hε).O : Type)ˣ) :
      ((ainfTowerL p O hv ε hε).O : Type)) = ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt := by
    show zetaV p O ε 0 = _
    simp [zetaV, root, fontaineTheta_teichmuller]
  rw [hz]
  clear hz
  haveI : NoZeroDivisors O :=
    hv.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  set z := ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt with hzdef
  clear_value z
  rw [h2] at hε
  exact hε.eq_neg_one_of_two_right

end ReciprocityTheory.PGsh.Be2
end
end

