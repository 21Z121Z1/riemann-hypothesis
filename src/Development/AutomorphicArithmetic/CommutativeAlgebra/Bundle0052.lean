import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CongruenceCRTOfLatticeGen
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

namespace UpperTheory.Gal.Int.Geo.CRT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

private theorem isInt_one' : IsIntAf (1 : AfP p) := fun v => by
  rw [map_one]; exact one_mem _

private theorem inAf_mem' (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, isInt_one', rfl⟩

private theorem mulF_tmul (c : 𝓞 D.F) (a : AfP p) (t : ℚ) (x : D.La) :
    mulF D c (a ⊗ₜ (t ⊗ₜ x)) = a ⊗ₜ (t ⊗ₜ (algebraMap (𝓞 D.F) D.O c • x)) := by
  simp [mulF, actQ]
  rfl

private theorem mulF_inAf (c : 𝓞 D.F) (x : D.La) :
    mulF D c (inAf D x) = inAf D (algebraMap (𝓞 D.F) D.O c • x) := mulF_tmul c 1 1 x

private theorem vq_induction {P : AfP p ⊗[ℚ] VQ D → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (ht : ∀ (a : AfP p) (t : ℚ) (x : D.La), P (a ⊗ₜ (t ⊗ₜ x))) (v : AfP p ⊗[ℚ] VQ D) : P v :=
  _root_.UpperTheory.Reformulated.B.Qk61.vq_induction h0 hadd ht v

private theorem mulF_mul (c d : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) : mulF D (c * d) v = mulF D c (mulF D d v) := by
  refine vq_induction (P := fun v => mulF D (c * d) v = mulF D c (mulF D d v)) (by simp) ?_ ?_ v
  · intro x y hx hy; simp only [map_add, hx, hy]
  · intro a t x; simp only [mulF_tmul, map_mul, mul_smul]

private theorem mulF_add (c d : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) : mulF D (c + d) v = mulF D c v + mulF D d v := by
  refine vq_induction (P := fun v => mulF D (c + d) v = mulF D c v + mulF D d v) (by simp) ?_ ?_ v
  · intro x y hx hy; simp only [map_add, hx, hy]; abel
  · intro a t x; simp only [mulF_tmul, map_add, add_smul, TensorProduct.tmul_add]

private theorem mulF_one (v : AfP p ⊗[ℚ] VQ D) : mulF D 1 v = v := by
  refine vq_induction (P := fun v => mulF D 1 v = v) (by simp) ?_ ?_ v
  · intro x y hx hy; simp only [map_add, hx, hy]
  · intro a t x; simp only [mulF_tmul, map_one, one_smul]

private theorem mulF_nat (n : ℕ) (v : AfP p ⊗[ℚ] VQ D) : mulF D (n : 𝓞 D.F) v = n • v := by
  induction n with
  | zero =>
    refine vq_induction (P := fun v => mulF D ((0 : ℕ) : 𝓞 D.F) v = (0 : ℕ) • v) (by simp) ?_ ?_ v
    · intro x y hx hy; simp only [map_add, hx, hy]; simp
    · intro a t x; simp [mulF_tmul]
  | succ n ih => rw [Nat.cast_succ, mulF_add, mulF_one, ih, succ_nsmul]

private theorem mulF_mem (c : 𝓞 D.F) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : mulF D c v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    rw [mulF_tmul]
    exact AddSubgroup.subset_closure ⟨a, _, ha, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

private theorem mem_idHat {𝔟 : Ideal (𝓞 D.F)} {x : 𝓞 D.F} (hx : x ∈ 𝔟) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    mulF D x v ∈ idHat D 𝔟 := AddSubgroup.subset_closure ⟨x, hx, v, hv, rfl⟩

private theorem idHat_ind {𝔟 : Ideal (𝓞 D.F)} {S : AddSubgroup (AfP p ⊗[ℚ] VQ D)}
    (h : ∀ x ∈ 𝔟, ∀ v ∈ LaHat D, mulF D x v ∈ S) : idHat D 𝔟 ≤ S :=
  (AddSubgroup.closure_le _).2 (by rintro _ ⟨x, hx, v, hv, rfl⟩; exact h x hx v hv)

private theorem idHat_mono {𝔟 𝔠 : Ideal (𝓞 D.F)} (h : 𝔟 ≤ 𝔠) : idHat D 𝔟 ≤ idHat D 𝔠 :=
  idHat_ind fun _ hx _ hv => mem_idHat (h hx) hv

private theorem mulF_mem_idHat_mul {𝔟 𝔠 : Ideal (𝓞 D.F)} {c : 𝓞 D.F} (hc : c ∈ 𝔠) {v : AfP p ⊗[ℚ] VQ D}
    (hv : v ∈ idHat D 𝔟) : mulF D c v ∈ idHat D (𝔠 * 𝔟) := by
  have : idHat D 𝔟 ≤ (idHat D (𝔠 * 𝔟)).comap (mulF D c).toAddMonoidHom := idHat_ind fun x hx w hw => by
    change mulF D c (mulF D x w) ∈ idHat D (𝔠 * 𝔟)
    rw [← mulF_mul]
    exact mem_idHat (Ideal.mul_mem_mul hc hx) hw
  exact this hv

private theorem actOn_comm (L : Link D G) (y : AfP p ⊗[ℚ] G.C) (b : D.O) :
    actOn L.rep (AfP p) y * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * actOn L.rep (AfP p) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]
  | tmul r c =>
    have e : actOn L.rep (AfP p) (r ⊗ₜ c) = r • (L.rep c).baseChange (AfP p) := by
      have e0 : actOn L.rep (AfP p) (r ⊗ₜ c) =
          (Algebra.ofId (AfP p) (Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) r) * (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) (L.rep c) :=
        Algebra.TensorProduct.lift_tmul _ _ _ _ _
      rw [e0, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, _root_.one_mul]
      rfl
    have h := (L.rep_range (L.rep c)).1 ⟨c, rfl⟩ b
    have h2 : (L.rep c).baseChange (AfP p) * (actQ D b).baseChange (AfP p) =
        (actQ D b).baseChange (AfP p) * (L.rep c).baseChange (AfP p) := by
      have := congrArg (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) h
      rw [map_mul, map_mul] at this
      exact this
    rw [e, smul_mul_assoc, mul_smul_comm, h2]

private theorem actG_mulF (L : Link D G) (g : G.GAf) (c : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG g (mulF D c v) = mulF D c (L.actG g v) :=
  LinearMap.congr_fun (actOn_comm L _ (algebraMap (𝓞 D.F) D.O c)) v

private theorem wSub_inAf {𝔞 : Ideal (𝓞 D.F)} {y : D.La} (hy : y ∈ wSub D 𝔞 1) : inAf D y ∈ idHat D 𝔞 := by
  have key : ∀ b : D.O, inAf D (b • y) ∈ idHat D 𝔞 := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, hc, z', rfl⟩ := hz
      intro b
      rw [pow_one] at hc
      have e : b • algebraMap (𝓞 D.F) D.O c • z' = algebraMap (𝓞 D.F) D.O c • b • z' := by
        rw [smul_smul, smul_smul, Algebra.commutes]
      rw [e, ← mulF_inAf]
      exact mem_idHat hc (inAf_mem' _)
    | zero =>
      intro b
      rw [smul_zero]
      have : inAf D (0 : D.La) = 0 := by simp [inAf]
      rw [this]; exact zero_mem _
    | add x z _ _ hx hz =>
      intro b
      have : inAf D (b • (x + z)) = inAf D (b • x) + inAf D (b • z) := by
        simp [inAf, smul_add, TensorProduct.tmul_add]
      rw [this]; exact add_mem (hx b) (hz b)
    | smul c x _ hx =>
      intro b
      rw [smul_smul]; exact hx _
  simpa using key 1

private theorem div_of_idHat {𝔟 : Ideal (𝓞 D.F)} {c : 𝓞 D.F} {N : ℕ} (h : ∀ x ∈ 𝔟, ∃ z : 𝓞 D.F, c * x = N * z)
    {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ idHat D 𝔟) : ∃ w ∈ LaHat D, mulF D c v = N • w := by
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hu
    obtain ⟨z, hz⟩ := h x hx
    exact ⟨mulF D z w, mulF_mem z hw, by rw [← mulF_mul, hz, mulF_mul, mulF_nat]⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, ew⟩ := hx
    obtain ⟨w', hw', ew'⟩ := hy
    exact ⟨w + w', add_mem hw hw', by rw [map_add, ew, ew', smul_add]⟩
  | neg x _ hx =>
    obtain ⟨w, hw, ew⟩ := hx
    exact ⟨-w, neg_mem hw, by rw [map_neg, ew, smul_neg]⟩

private theorem crt_part (L : Link D G) (N₀ : ℕ) (𝔞 : Ideal (𝓞 D.F)) (s t : 𝓞 D.F) (ht : t ∈ 𝔞)
    (e : (N₀ : 𝓞 D.F) * s + t = 1) (g : G.GAf) :
    CongId L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) g ↔ L.CongOne N₀ g ∧ CongId L 𝔞 g := by
  have hN : (N₀ : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} := Ideal.mem_span_singleton_self _
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v hv => idHat_mono Ideal.mul_le_right (h v hv)⟩
    obtain ⟨w, hw, ew⟩ := div_of_idHat (c := 1) (N := N₀) (fun x hx => by
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.mul_le_left hx)
      exact ⟨z, by rw [_root_.one_mul, ← hz, _root_.mul_comm]⟩) (h v hv)
    rw [mulF_one] at ew
    refine ⟨w, hw, ?_⟩
    rw [← ew]; abel
  · rintro ⟨h1, h2⟩ v hv
    obtain ⟨w, hw, ew⟩ := h1 v hv
    have hu : L.actG g v - v = N₀ • w := by rw [ew]; abel
    have hu2 := h2 v hv
    have dec : L.actG g v - v = mulF D ((N₀ : 𝓞 D.F) * s) (L.actG g v - v) + mulF D t (L.actG g v - v) := by
      rw [← mulF_add, e, mulF_one]
    rw [dec]
    refine add_mem (mulF_mem_idHat_mul (Ideal.mul_mem_right _ _ hN) hu2) ?_
    rw [hu, ← mulF_nat, ← mulF_mul, _root_.mul_comm t]
    exact mem_idHat (Ideal.mul_mem_mul hN ht) hw

private theorem bezout {q N₀ : ℕ} {r : ℤ} {𝔞 : Ideal (𝓞 D.F)} (hc : N₀.Coprime q) (e : ℕ) (he : uId D q r ^ e ≤ 𝔞) :
    ∃ s t : 𝓞 D.F, t ∈ 𝔞 ∧ (N₀ : 𝓞 D.F) * s + t = 1 := by
  have hq : ((q : 𝓞 D.F)) ^ e ∈ 𝔞 :=
    he (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_insert _ _)) e)
  have hc' : IsCoprime (N₀ : ℤ) ((q ^ e : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right e hc)
  obtain ⟨u, v, huv⟩ := hc'
  refine ⟨(u : 𝓞 D.F), (v : 𝓞 D.F) * (q : 𝓞 D.F) ^ e, Ideal.mul_mem_left _ _ hq, ?_⟩
  have := congrArg (Int.cast : ℤ → 𝓞 D.F) huv
  push_cast at this
  rw [← this]; ring

private theorem gen_part (hLG : LatGen) (L : Link D G) (𝔞 : Ideal (𝓞 D.F)) (g : G.GAf) (hg : Integ L g)
    (a : 𝓞 D.F) (N : ℕ) (hN : 0 < N) (hNp : N.Coprime p) (hgen : IsGen a N 𝔞) :
    CongId L 𝔞 g ↔ ∀ y : D.La, ∃ v ∈ LaHat D,
      L.actG g (inAf D (algebraMap (𝓞 D.F) D.O a • y)) = inAf D (algebraMap (𝓞 D.F) D.O a • y) + N • v := by
  have hNa : (N : 𝓞 D.F) ∈ 𝔞 := by
    have : (N : 𝓞 D.F) ∈ (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞 := by
      rw [show (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞 = _ from hgen]
      exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_right this
  have hax : ∀ x ∈ 𝔞, ∃ z : 𝓞 D.F, a * x = N * z := fun x hx => by
    have : a * x ∈ Ideal.span {(N : 𝓞 D.F)} := by
      rw [← show (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞 = _ from hgen]
      exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) hx
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨z, by rw [← hz, _root_.mul_comm]⟩
  constructor
  · intro h y
    obtain ⟨w, hw, ew⟩ := div_of_idHat hax (h _ (inAf_mem' y))
    refine ⟨w, hw, ?_⟩
    rw [map_sub, ← actG_mulF, mulF_inAf] at ew
    rw [← ew]; abel
  · intro h
    have step1 : ∀ v ∈ LaHat D, ∃ w ∈ LaHat D, mulF D a (L.actG g v - v) = N • w := fun v hv => by
      obtain ⟨x, w', hw', rfl⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N hN hNp v hv
      obtain ⟨v₁, hv₁, e₁⟩ := h x
      refine ⟨v₁ + mulF D a (L.actG g w' - w'), add_mem hv₁ (mulF_mem a (sub_mem (hg _ hw') hw')), ?_⟩
      have e₂ : mulF D a (L.actG g (inAf D x) - inAf D x) = N • v₁ := by
        rw [map_sub, ← actG_mulF, mulF_inAf, e₁]; abel
      have e₃ : L.actG g (inAf D x + N • w') - (inAf D x + N • w') =
          (L.actG g (inAf D x) - inAf D x) + N • (L.actG g w' - w') := by
        rw [map_add, map_nsmul, smul_sub]; abel
      rw [e₃, map_add, e₂, map_nsmul, smul_add]
    intro v hv
    have hu : L.actG g v - v ∈ LaHat D := sub_mem (hg v hv) hv
    obtain ⟨w₁, hw₁, e₁⟩ := step1 v hv
    obtain ⟨y, w, hw, e₂⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N hN hNp _ hu
    have hdvd : ∃ u : D.La, algebraMap (𝓞 D.F) D.O a • y = N • u := by
      refine GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul p D N hN hNp (GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP p N hN hNp) _ ⟨w₁ - mulF D a w, sub_mem hw₁ (mulF_mem a hw), ?_⟩
      rw [e₂, map_add, mulF_inAf, map_nsmul] at e₁
      rw [smul_sub, ← e₁]; abel
    have hy : y ∈ wSub D 𝔞 1 := ((hLG p D a N 𝔞 hN hgen).1 y).1 hdvd
    rw [e₂]
    refine add_mem (wSub_inAf hy) ?_
    rw [← mulF_nat]
    exact mem_idHat hNa hw

end UpperTheory.Gal.Int.Geo.CRT

open UpperTheory.Gal.Int.Geo.CRT in
theorem UpperTheory.congruenceCRT_of_latticeGen :
    LatGen → CongCRT := by
  intro hLG p _ D G L q r N₀ 𝔞 hc ⟨e, he⟩ g hg
  obtain ⟨s, t, ht, est⟩ := bezout hc e he
  exact ⟨crt_part L N₀ 𝔞 s t ht est g, fun a N hN hNp hgen => gen_part hLG L 𝔞 g hg a N hN hNp hgen⟩

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeCorrespondenceIsogenyOfTraceCrt
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct
open GlobalTheory.CechPic
open UpperTheory.Gal.Int.Geo

section Over

variable {X : Scheme.{0}} {U V A B : Over X} [GrpObj U] [GrpObj V] [GrpObj A] [GrpObj B]

private theorem cartIso {φ : A.left ⟶ B.left} (h : IsGrpPullback A B (𝟙 X) φ) :
    ∃ e : A ≅ B, e.hom.left = φ ∧ IsMonHom e.hom := by
  haveI : IsIso φ := h.1.isIso_fst_of_isIso
  have hw : φ ≫ B.hom = A.hom := by simpa using h.1.w
  have he : (Over.isoMk (asIso φ) hw).hom.left = φ := rfl
  refine ⟨Over.isoMk (asIso φ) hw, rfl, ?_⟩
  apply GlobalTheory.GrpPullPow.isMonHom_of_mul_pts
  intro T x y
  apply Over.OverMorphism.ext
  let j : Over.mk (T.hom ≫ 𝟙 X) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key := h.2 T x y (j ≫ x ≫ (Over.isoMk (asIso φ) hw).hom) (j ≫ y ≫ (Over.isoMk (asIso φ) hw).hom)
    (by simp [j, he]) (by simp [j, he])
  rw [← MonObj.comp_mul] at key
  simpa [j, he] using key.symm

private theorem quasiInv (e₁ : U ≅ A) (e₂ : V ≅ B) [IsMonHom e₁.hom] (ψ : U ⟶ V) (ψ' : V ⟶ U) (n : ℕ)
    (h : ψ ≫ ψ' = 𝟙 U ^ n) : (e₁.inv ≫ ψ ≫ e₂.hom) ≫ e₂.inv ≫ ψ' ≫ e₁.hom = 𝟙 A ^ n := by
  have h2 : (e₁.inv ≫ ψ ≫ e₂.hom) ≫ e₂.inv ≫ ψ' ≫ e₁.hom = e₁.inv ≫ (ψ ≫ ψ') ≫ e₁.hom := by simp
  rw [h2, h, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Iso.inv_hom_id]

private theorem kerIff (e₁ : U ≅ A) (e₂ : V ≅ B) [IsMonHom e₂.hom] (ψ : U ⟶ V) {T : Over X} (g : T ⟶ U) :
    (g ≫ e₁.hom) ≫ e₁.inv ≫ ψ ≫ e₂.hom = 1 ↔ g ≫ ψ = 1 := by
  have e : (g ≫ e₁.hom) ≫ e₁.inv ≫ ψ ≫ e₂.hom = (g ≫ ψ) ≫ e₂.hom := by simp
  rw [e]
  refine ⟨fun h => ?_, fun h => by rw [h, one_comp]⟩
  have := congrArg (· ≫ e₂.inv) h
  simpa [one_comp] using this

end Over

private theorem isoEqOne {X : Scheme.{0}} {A B : Over X} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] {T : Over X} (y : T ⟶ A) :
    y ≫ e.hom = 1 ↔ y = 1 := by
  constructor
  · intro h
    have h' : y = (y ≫ e.hom) ≫ e.inv := by simp
    rw [h', h, MonObj.one_comp]
  · rintro rfl
    exact MonObj.one_comp _

section Pol

variable {X : Scheme.{0}} {U V A B : Over X} [GrpObj U] [IsCommMonObj U] [GrpObj V] [IsCommMonObj V]
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

private theorem square_id : Hecke.sq2 (𝟙 B) = 𝟙 (G2 B).left := by
  unfold Hecke.sq2
  simp

private theorem isIso_sq (e : A ≅ B) {φ₂ : (G2 A).left ⟶ (G2 B).left} (h : Geo.Tor.IsSquare e.hom.left φ₂) :
    IsIso φ₂ := by
  have hsq : Geo.Tor.IsSquare (𝟙 A.left) (𝟙 (G2 A).left) := by
    constructor <;> simp
  have key := ES.PIsogExt.isSquare_square_compatible_homs hsq h (ψ₀ := 𝟙 A) (ψ := e.hom) (by simp)
  rw [square_id, Category.id_comp, Category.id_comp] at key
  rw [← key]
  refine ⟨⟨Hecke.sq2 e.inv, ?_, ?_⟩⟩
  · rw [← Hecke.Comp.grpSchemeSquareProductMap_comp, e.hom_inv_id, square_id]
  · rw [← Hecke.Comp.grpSchemeSquareProductMap_comp, e.inv_hom_id, square_id]

private theorem polMove {PU : LB (G2 U).left} {PV : LB (G2 V).left} {PA : LB (G2 A).left} {PB : LB (G2 B).left}
    (hU : PU.IsLB) (hV : PV.IsLB) (hA : PA.IsLB) (hB : PB.IsLB) (e₁ : U ≅ A) (e₂ : V ≅ B) (ψ : U ⟶ V) (χ : A ⟶ B)
    (he : e₁.hom.left ≫ χ.left = ψ.left ≫ e₂.hom.left) {φ₁ : (G2 U).left ⟶ (G2 A).left} {φ₂ : (G2 V).left ⟶ (G2 B).left}
    (s₁ : Geo.Tor.IsSquare e₁.hom.left φ₁) (s₂ : Geo.Tor.IsSquare e₂.hom.left φ₂)
    (l₁ : LBIso PU (PA.pull φ₁)) (l₂ : LBIso PV (PB.pull φ₂)) (c : ℕ)
    (l : LBIso (Hecke.lbPow PU c) (PV.pull (Hecke.sq2 ψ))) :
    LBIso (Hecke.lbPow PA c) (PB.pull (Hecke.sq2 χ)) := by
  haveI : IsIso φ₁ := isIso_sq e₁ s₁
  have key : φ₁ ≫ Hecke.sq2 χ = Hecke.sq2 ψ ≫ φ₂ := ES.PIsogExt.isSquare_square_compatible_homs s₁ s₂ he
  have hPAc : (Hecke.lbPow PA c).IsLB := LB.isLB_linComb hA _ _
  have hPUc : (Hecke.lbPow PU c).IsLB := LB.isLB_linComb hU _ _
  have hPBχ : (PB.pull (Hecke.sq2 χ)).IsLB := pull_isLB hB _
  rw [← cls_eq_iff hPAc hPBχ]
  have inj : ∀ x y : Pic (G2 A).left, pull φ₁ x = pull φ₁ y → x = y := by
    intro x y hxy
    have hh := congrArg (pull (inv φ₁)) hxy
    rwa [← pull_comp, ← pull_comp, IsIso.inv_hom_id, pull_id, pull_id] at hh
  have h1 : cls PU hU = pull φ₁ (cls PA hA) := by
    rw [← cls_pull hA φ₁ (pull_isLB hA φ₁)]
    exact (cls_eq_iff _ _).2 l₁
  have h2 : cls PV hV = pull φ₂ (cls PB hB) := by
    rw [← cls_pull hB φ₂ (pull_isLB hB φ₂)]
    exact (cls_eq_iff _ _).2 l₂
  have h3 : cls (Hecke.lbPow PU c) hPUc = cls (PV.pull (Hecke.sq2 ψ)) (pull_isLB hV _) := (cls_eq_iff _ _).2 l
  rw [Hecke.Comp.cls_lbPow' hU c hPUc, cls_pull hV] at h3
  apply inj
  rw [Hecke.Comp.cls_lbPow' hA c hPAc, cls_pull hB _ hPBχ, map_nsmul, ← h1, h3, h2, ← pull_comp,
    ← pull_comp, key]

end Pol

private theorem intMul {p : ℕ} [Fact p.Prime] {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

private theorem inAf_mem {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

private theorem numEq {p : ℕ} [Fact p.Prime] {c₀ M : ℕ} (hc : c₀.Coprime p) (hM : M.Coprime p) {t t' t₁ t₁' m₀ t₂ : AfP p}
    (ht : IsIntAf t) (ht' : IsIntAf t') (htt : t * t' = 1) (i1 : IsIntAf t₁) (i1' : IsIntAf t₁') (e1 : t₁ * t₁' = 1)
    (im₀ : IsIntAf m₀) (i2 : IsIntAf t₂) (e2 : m₀ * t₂ = 1) (e : (M : AfP p) * t₁ * m₀ = c₀ * t)
    (H : ∀ (c c' : ℕ) (t t' : AfP p), c.Coprime p → c'.Coprime p → IsIntAf t → IsIntAf t' → t * t' = 1 → (c : AfP p) = c' * t → c = c') :
    c₀ = M := by
  refine H c₀ M (t₁ * m₀ * t') (t₁' * t₂ * t) hc hM (intMul (intMul i1 im₀) ht') (intMul (intMul i1' i2) ht) ?_ ?_
  · calc t₁ * m₀ * t' * (t₁' * t₂ * t) = (t₁ * t₁') * (m₀ * t₂) * (t * t') := by ring
      _ = 1 := by rw [e1, e2, htt]; ring
  · calc (c₀ : AfP p) = c₀ * t * t' := by rw [_root_.mul_assoc, htt, _root_.mul_one]
      _ = M * (t₁ * m₀ * t') := by rw [← e]; ring

theorem UpperTheory.heckeCorrespondence_isogeny_of_trace_crt :
    TrEta → TrBack → TrTj → MultUnit → CongCRT → TjIsog := by
  intro hTE hTB hTT hMU hCRT
  intro p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hTj hIh u hu N' N c' c hN' hN W s₀ o₁ o₂ n₁ n₂
  obtain ⟨hu1, huC⟩ := (hLev u).1 hu
  have hIu : Integ L u := integ_of_mem hu1
  rw [S.lev] at huC
  have huN₀ : L.CongOne S.N₀ u := ((hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow u hIu).1.1 huC).1
  have hhN₀ : L.CongOne S.N₀ h := hTj.away S.N₀ S.std.cop
  have hhu : L.CongOne S.N₀ (h * u) := Link.CongOne.mul L hhN₀ huN₀
  obtain ⟨e₁, he₁, hm₁⟩ := cartIso n₁.cart
  obtain ⟨e₂, he₂, hm₂⟩ := cartIso n₂.cart
  haveI := hm₁
  haveI := hm₂
  haveI : IsMonHom W.ψ := W.trans.1
  have hM : Ideal.absNorm 𝔴 ^ i = q ^ (S.f * i) := by
    rw [S.std.norm, pow_mul]
  have hqp : q.Coprime p := (Nat.coprime_primes (Fact.out) (Fact.out)).2 S.atq.ne
  have hMcop : (q ^ (S.f * i)).Coprime p := Nat.Coprime.pow_left _ hqp
  have hsq : n₁.φ ≫ Over.Hom.left (e₁.inv ≫ W.ψ ≫ e₂.hom) = Over.Hom.left W.ψ ≫ n₂.φ := by
    rw [← he₁, ← he₂]
    simp only [Over.comp_left]
    rw [← Category.assoc, ← Over.comp_left, e₁.hom_inv_id]
    simp
  have a1 : ∀ d : D.O, (T.M N').univ.act.act d ≫ e₁.hom = e₁.hom ≫ o₁.act.act d := by
    intro d
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, he₁]
    exact n₁.act d
  have a1' : ∀ d : D.O, o₁.act.act d ≫ e₁.inv = e₁.inv ≫ (T.M N').univ.act.act d := by
    intro d
    rw [Iso.comp_inv_eq, Category.assoc, a1, Iso.inv_hom_id_assoc]
  have a2 : ∀ d : D.O, W.o.act.act d ≫ e₂.hom = e₂.hom ≫ o₂.act.act d := by
    intro d
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, he₂]
    exact n₂.act d
  refine ⟨e₁.inv ≫ W.ψ ≫ e₂.hom, hsq, ?_, ?_⟩
  · refine ⟨⟨S.f * i, rfl⟩, inferInstance, ?_, ?_, ?_, ?_⟩
    · intro d
      rw [reassoc_of% (a1' d), reassoc_of% (W.trans.2.1 d), a2]
      simp only [Category.assoc]
    · intro x
      have b1' : (T.M N').univ.eta (c' • x) ≫ e₁.hom = o₁.eta x := by
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, he₁]
        simpa using n₁.eta x
      have b1 : o₁.eta x ≫ e₁.inv = (T.M N').univ.eta (c' • x) := by
        rw [Iso.comp_inv_eq]
        exact b1'.symm
      have b2 : W.o.eta (c • x) ≫ e₂.hom = o₂.eta x := by
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, he₂]
        simpa using n₂.eta x
      have b3 : (T.M N').univ.eta (c' • x) ≫ W.ψ = W.o.eta (c • x) :=
        hTE p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ W.trans S.N₀ c' c hN' hN
          x x (hhu _ (inAf_mem D x))
      rw [reassoc_of% b1, reassoc_of% b3, b2]
    · obtain ⟨c₀, hc₀, ⟨hl⟩, t, t', ht, ht', htt, hmul⟩ := W.trans.2.2.2.1
      obtain ⟨t₁, t₁', i1, i1', e1, hh⟩ := hTj.mult
      obtain ⟨t₂, im₀, i2, e2⟩ := (hMU p D G L).1 u hu1
      have hc : c₀ = q ^ (S.f * i) := by
        refine numEq hc₀ hMcop ht ht' htt i1 i1' e1 im₀ i2 e2 ?_ (hMU p D G L).2
        rw [← hmul, ← hM]
        push_cast at hh ⊢
        rw [← hh]
        simp [Units.val_mul]
      rw [← hc]
      refine ⟨polMove (T.M N').univ.isLB W.o.isLB o₁.isLB o₂.isLB e₁ e₂ W.ψ (e₁.inv ≫ W.ψ ≫ e₂.hom) ?_
        (by rw [he₁]; exact n₁.sq) (by rw [he₂]; exact n₂.sq) n₁.pol n₂.pol c₀ hl⟩
      rw [he₁, he₂]
      exact hsq
    · have hback : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, (L.actG (h * u)) v' = (q ^ (S.f * i)) • v := by
        intro v hv
        obtain ⟨v'', hv'', hvv⟩ := hTj.back v hv
        have hui : L.CongOne 1 u⁻¹ := hu1.2
        obtain ⟨w₁, hw₁, hw⟩ := hui v'' hv''
        refine ⟨L.actG u⁻¹ v'', ?_, ?_⟩
        · rw [hw, one_smul]
          exact add_mem hv'' hw₁
        · rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (L.actG u), ← map_mul, mul_inv_cancel,
            map_one, Module.End.one_apply, hvv, hM]
      obtain ⟨ψ', hψ', h1, h2⟩ := hTB p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ
        W.trans _ hMcop hback
      haveI := hψ'
      exact ⟨e₂.inv ≫ ψ' ≫ e₁.hom, inferInstance, quasiInv e₁ e₂ W.ψ ψ' _ h1, quasiInv e₂ e₁ ψ' W.ψ _ h2⟩
  · intro kk _ _ _ x
    obtain ⟨hT1, hT2⟩ := hTT p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ W.trans q r 𝔴
      i h u S.atq hTj hIh hu1 rfl kk x
    have hk : ∀ (g : Over.mk x ⟶ o₁.A) (d : D.O), g ≫ o₁.act.act d = 1 ↔ (g ≫ e₁.inv) ≫ (T.M N').univ.act.act d = 1 := by
      intro g d
      rw [Category.assoc, ← a1' d, ← Category.assoc]
      haveI : IsMonHom e₁.symm.hom := (inferInstance : IsMonHom e₁.inv)
      exact (isoEqOne e₁.symm (g ≫ o₁.act.act d)).symm
    have hker : ∀ g : Over.mk x ⟶ o₁.A, g ≫ (e₁.inv ≫ W.ψ ≫ e₂.hom) = 1 ↔ (g ≫ e₁.inv) ≫ W.ψ = 1 := by
      intro g
      have := kerIff e₁ e₂ W.ψ (g ≫ e₁.inv)
      simpa using this
    refine ⟨?_, ?_⟩
    · intro g hg ⟨e, he⟩ a ha
      rw [hk]
      refine hT1 (g ≫ e₁.inv) ((hker g).1 hg) ⟨e, fun y hy => (hk g _).1 (he y hy)⟩ a ha
    · rw [S.std.m1, _root_.one_mul, ← hT2]
      refine Nat.card_congr (Equiv.subtypeEquiv
        ⟨fun g => g ≫ e₁.inv, fun g => g ≫ e₁.hom, fun g => by simp, fun g => by simp⟩ ?_)
      intro g
      refine and_congr (hker g) ?_
      exact forall₂_congr fun a _ => hk g _
end
end

