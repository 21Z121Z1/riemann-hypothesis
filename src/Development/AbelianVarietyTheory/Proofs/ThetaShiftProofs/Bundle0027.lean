import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RepTransport
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj

namespace GlobalTheory.FibreFrame

variable {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] {X Y Z : Scheme.{0}} {L : LB Z} {m : ℕ}

theorem le_wchart {π : X ⟶ Z} {q : Sp R ⟶ X} {j : L.ι} (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => h hz

theorem sval_spMap {π : X ⟶ Z} (s : SecP L π m) (ρ : R →+* R') (q : Sp R ⟶ X) {j : L.ι}
    (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) : ArcPts.sval s (spMap ρ ≫ q) j = ρ (ArcPts.sval s q j) :=
  HolHom.valR_spMap ρ q _ (le_wchart h) _

theorem exists_pull {π : X ⟶ Z} (s : SecP L π m) (h : Y ⟶ X) {π' : Y ⟶ Z} (e : h ≫ π = π') :
    ∃ s' : SecP L π' m, (∀ j (le : LB.wchart L (fun _ : Fin 1 => π') j ≤ h ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) j),
        s'.f j = (Y.presheaf.map (homOfLE le).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (R : Type) [CommRing R] (q : Sp R ⟶ Y) (j : L.ι), ⊤ ≤ (q ≫ π') ⁻¹ᵁ L.U j →
        ArcPts.sval s' q j = ArcPts.sval s (q ≫ h) j := by
  subst e
  refine ⟨DVR.pullSec L (fun _ : Fin 1 => π) (fun _ => (m : ℤ)) s h, fun _ _ => rfl, fun R _ q j hj => ?_⟩
  exact (HolHom.valR_res q _ _ (le_wchart hj)).trans (HolHom.valR_comp q h _ _).symm

theorem res_constFn (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a :=
  congrArg (fun q : Γ(Sp K, ⊤) ⟶ Γ(X, V) => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)

theorem valR_constFn (p : X ⟶ Sp K) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, Conv.valR_spMap_top]

def comb (p : X ⟶ Sp K) {M : LB X} {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) : M.Sec where
  f j := ∑ i, constFn p _ (r i) * (σ i).f j
  compat j k := by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (σ i).compat j k]
    ring

theorem valR_comb (p : X ⟶ Sp K) {M : LB X} {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : M.ι) (h : ⊤ ≤ q ⁻¹ᵁ M.U j) :
    valR q _ ((comb p r σ).f j) = ∑ i, f (r i) * valR q _ ((σ i).f j) := by
  simp only [← valR_constFn p f q hq _ h, HolHom.valR_eq _ _ h, comb, map_sum, map_mul]

theorem sval_comb {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (r : Fin n → K) (σ : Fin n → SecP L π m) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) {j : L.ι} (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ArcPts.sval (comb p r σ : SecP L π m) q j = ∑ i, f (r i) * ArcPts.sval (σ i) q j := by
  exact valR_comb p r σ f q hq (fun _ => j) (le_wchart h)

theorem ext_sval {π : X ⟶ Z} {s s' : SecP L π m}
    (h : ∀ (R : Type) [CommRing R] (q : Sp R ⟶ X) (j : L.ι), ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j →
      ArcPts.sval s q j = ArcPts.sval s' q j) (j : Fin 1 → L.ι) : s.f j = s'.f j := by
  obtain ⟨j, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim _ _)⟩
  refine TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx => ?_
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) hx
  obtain ⟨q, hq, hv⟩ := Conv.exists_point_of_ringHom hV (RingHom.id _)
  have hle' : V ≤ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) := hle
  have e := h _ q j fun z hz => LB.wchart_le L (fun _ : Fin 1 => π) (fun _ => j) 0 (hle' (hq hz))
  have e1 := (hv _).symm.trans (HolHom.valR_res q hle' (s.f fun _ => j) hq)
  have e2 := (hv _).symm.trans (HolHom.valR_res q hle' (s'.f fun _ => j) hq)
  exact X.presheaf.germ_ext V hxV (homOfLE hle') (homOfLE hle') (e1.trans (e.trans e2.symm))

def Rep {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (s : SecP L π m) (c : Fin n → K) : Prop :=
  ∀ (R : Type) [CommRing R] (f : K →+* R) (q : Sp R ⟶ X) (j : L.ι), q ≫ p = spMap f → ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j →
    ArcPts.sval s q j = ∑ i, f (c i) * ArcPts.sval (σ i) q j

theorem rep_comb {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (c : Fin n → K) :
    Rep p σ (comb p c σ) c := fun _ _ f q _ hq h => sval_comb p c σ f q hq h

theorem rep_iff {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (s : SecP L π m) (c : Fin n → K) :
    Rep p σ s c ↔ ∀ j, s.f j = (comb p c σ).f j := by
  refine ⟨fun H => ext_sval fun R _ q j hj => ?_, fun H R _ f q j hq hj => ?_⟩
  · have hq : q ≫ p = spMap (Spec.preimage (q ≫ p)).hom := (Spec.map_preimage _).symm
    exact (H R _ q j hq hj).trans (sval_comb p c σ _ q hq hj).symm
  · exact (congrArg (valR q _) (H _)).trans (sval_comb p c σ f q hq hj)

theorem rep_transport {π : X ⟶ Z} {p : X ⟶ Sp K} {n : ℕ} {σ : Fin n → SecP L π m} (e : Y ≅ X) {π' : Y ⟶ Z}
    {p' : Y ⟶ Sp K} (hπ : e.hom ≫ π = π') (hp : e.hom ≫ p = p') {σ' : Fin n → SecP L π' m}
    (hσ : ∀ i (R : Type) [CommRing R] (q : Sp R ⟶ Y) (j : L.ι), ⊤ ≤ (q ≫ π') ⁻¹ᵁ L.U j →
      ArcPts.sval (σ' i) q j = ArcPts.sval (σ i) (q ≫ e.hom) j)
    (H : ∀ s, ∃! c, Rep p σ s c) (s' : SecP L π' m) : ∃! c, Rep p' σ' s' c := by
  subst hπ hp
  obtain ⟨s, -, hs⟩ := exists_pull s' e.inv (π' := π) (e.inv_hom_id_assoc π)
  have key : ∀ c, Rep (e.hom ≫ p) σ' s' c ↔ Rep p σ s c := fun c => by
    constructor
    · intro h R _ f q j hq hj
      have hj' : ⊤ ≤ ((q ≫ e.inv) ≫ e.hom ≫ π) ⁻¹ᵁ L.U j := by simpa using hj
      rw [hs R q j hj, h R f _ j (by simpa using hq) hj']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hσ i R _ j hj', Category.assoc, e.inv_hom_id, Category.comp_id]
    · intro h R _ f q j hq hj
      have hj' : ⊤ ≤ ((q ≫ e.hom) ≫ π) ⁻¹ᵁ L.U j := by simpa using hj
      have := h R f (q ≫ e.hom) j (by simpa using hq) hj'
      rw [hs R _ j hj', Category.assoc, e.hom_inv_id, Category.comp_id] at this
      rw [this]
      exact Finset.sum_congr rfl fun i _ => by rw [hσ i R _ j hj]
  simp only [key]
  exact H s

open Out in

theorem exists_frame (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ)
    (hn : 1 ≤ n) (x : S) : ∃ V : S.Opens, x ∈ V ∧ ∃ (N : ℕ) (β : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S),
      ⊤ ≤ y ⁻¹ᵁ V → Fin N → SecP P.L (pullback.fst P.A.hom y) n),
      (∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (R' : Type) [CommRing R'] (y' : Sp R' ⟶ S)
        (hy' : ⊤ ≤ y' ⁻¹ᵁ V) (C : Type) [CommRing C] (q : Sp C ⟶ pullback P.A.hom y) (q' : Sp C ⟶ pullback P.A.hom y')
        (i : Fin N) (j : P.L.ι), q ≫ pullback.fst _ _ = q' ≫ pullback.fst _ _ →
        ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ P.L.U j → ArcPts.sval (β R y hy i) q j = ArcPts.sval (β R' y' hy' i) q' j) ∧
      ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (s : SecP P.L (pullback.fst P.A.hom y) n),
        ∃! c, Rep (pullback.snd P.A.hom y) (β R y hy) s c := by
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn x
  let W := overRes (T := baseOver S) V
  have key : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S), ⊤ ≤ y ⁻¹ᵁ V →
      ∃ (k : pullback P.A.hom y ⟶ (W ⊗ P.A).left) (β : Fin (n ^ P.g) → SecP P.L (pullback.fst P.A.hom y) n),
        k ≫ (snd W P.A).left = pullback.fst _ _ ∧
        (∀ i (C : Type) [CommRing C] (q : Sp C ⟶ pullback P.A.hom y) (j : P.L.ι),
          ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ P.L.U j →
          ArcPts.sval (β i) q j = ArcPts.sval (m := n) (p := (snd W P.A).left) (b i) (q ≫ k) j) ∧
        ∀ s, ∃! c, Rep (pullback.snd P.A.hom y) β s c := by
    intro R _ y hy
    let t : Sp R ⟶ W.left := IsOpenImmersion.lift V.ι y (by
      rintro _ ⟨z, rfl⟩
      exact V.range_ι.ge (hy (x := z) trivial))
    have ht : (baseAt t).hom = y := by
      show t ≫ V.ι ≫ 𝟙 _ = y
      rw [Category.comp_id]
      exact IsOpenImmersion.lift_fac _ _ _
    have hp : IsPullback (pullback.snd P.A.hom y) (pullback.fst P.A.hom y) (baseAt t).hom P.A.hom :=
      ht ▸ (IsPullback.of_hasPullback P.A.hom y).flip
    let e : pullback P.A.hom y ≅ (baseAt t ⊗ P.A).left := hp.isoPullback
    have e₁ : e.hom ≫ (snd (baseAt t) P.A).left = pullback.fst _ _ := hp.isoPullback_hom_snd
    have e₂ : e.hom ≫ (fst (baseAt t) P.A).left = pullback.snd _ _ := hp.isoPullback_hom_fst
    have e₃ : (homAt t ▷ P.A).left ≫ (snd W P.A).left = (snd (baseAt t) P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)
    choose b' hb0 hb' using fun i => exists_pull (π := (snd W P.A).left) (m := n) (b i) (homAt t ▷ P.A).left e₃
    choose β _ hβ using fun i => exists_pull (b' i) e.hom e₁
    obtain ⟨hli, hsp⟩ := hb R t b' (fun i j => hb0 i j _)
    refine ⟨e.hom ≫ (homAt t ▷ P.A).left, β, (Category.assoc _ _ _).trans ((congrArg _ e₃).trans e₁), fun i C _ q j hj => ?_,
      rep_transport (p := (fst (baseAt t) P.A).left) e e₁ e₂ hβ fun s => ?_⟩
    · rw [hβ i C q j hj, hb' i C _ j (by rw [Category.assoc, e₁]; exact hj), Category.assoc]
    have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv
    have key : ∀ c : Fin (n ^ P.g) → R, Rep (fst (baseAt t) P.A).left b' s c ↔
        ∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) •
          (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t)) = SecM.ofSec P.A s := fun c => by
      have ev : ∀ j, (∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) •
          (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))).1 j =
          (comb (K := R) (fst (baseAt t) P.A).left c b').f j := fun j => by
        rw [Submodule.coe_sum, Finset.sum_apply]
        rfl
      rw [rep_iff]
      exact ⟨fun h => Subtype.ext (funext fun j => (ev j).trans (h j).symm),
        fun h j => (congrFun (congrArg Subtype.val h) j).symm.trans (ev j)⟩
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hsp.ge (Submodule.mem_top : SecM.ofSec P.A s ∈ ⊤))
    choose a ha using fun i => bij.2 (r i)
    obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i)) = r := funext ha
    refine ⟨a, (key a).2 hr, fun a' ha' => funext fun i => bij.1 ?_⟩
    exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key a').1 ha').trans hr.symm) i
  choose k β hk hβ hr using key
  refine ⟨V, hV, _, β, fun R _ y hy R' _ y' hy' C _ q q' i j hq hj => ?_, hr⟩
  have hm : Mono (snd W P.A).left := by
    have : Mono W.hom := inferInstanceAs (Mono (V.ι ≫ 𝟙 S))
    exact inferInstanceAs (Mono (pullback.snd W.hom P.A.hom))
  rw [hβ R y hy i C q j hj, hβ R' y' hy' i C q' j (hq ▸ hj)]
  congr 1
  rw [← cancel_mono (snd W P.A).left, Category.assoc, Category.assoc, hk, hk, hq]

end GlobalTheory.FibreFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaCharOffNeZeroDifferentiableQuasiPeriodic
section
noncomputable section

open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaBlock

variable {g : ℕ} {S : Finset (Fin g)}

def offEquiv (S : Finset (Fin g)) : {n : Fin g → ℤ // ∀ k ∈ S, n k = 0} ≃ ({k // k ∉ S} → ℤ) where
  toFun n i := n.1 i
  invFun l := ⟨fun k => if h : k ∈ S then 0 else l ⟨k, h⟩, fun k hk => dif_pos hk⟩
  left_inv n := by
    refine Subtype.ext (funext fun k => ?_)
    by_cases h : k ∈ S
    · simp [h, n.2 k h]
    · simp [h]
  right_inv l := by
    funext i
    simp [i.2]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem submatrix_mem_siegelH_of_posDef_im (S : Finset (Fin g)) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    τ.submatrix (Subtype.val : {k // k ∉ S} → Fin g) Subtype.val ∈ _root_.ReciprocityTheory.PTheta.SiegelH {k // k ∉ S} := by
  unfold _root_.ReciprocityTheory.PTheta.SiegelH
  exact ⟨hs.submatrix _, hp.submatrix Subtype.val_injective⟩

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem ofReal_re_eq_self_of_eq_zero_or_half {c : ℂ} (h : c = 0 ∨ c = 1 / 2) :
    ((c.re : ℝ) : ℂ) = c := by
  rcases h with rfl | rfl
  · simp
  · apply Complex.ext <;> simp

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem dotProduct_eq_restrict_of_vanishing (S : Finset (Fin g)) {v : Fin g → ℂ}
    (hv : ∀ k ∈ S, v k = 0) (w : Fin g → ℂ) :
    v ⬝ᵥ w = (fun i : {k // k ∉ S} => v i) ⬝ᵥ (fun i : {k // k ∉ S} => w i) := by
  unfold dotProduct
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => k ∉ S)]
  have h0 : ∑ i : {k // ¬ k ∉ S}, v i * w i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hv i (not_not.1 i.2), zero_mul]
  rw [h0, add_zero]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem mulVec_restrict_eq_submatrix_mulVec_of_vanishing (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ)
    {v : Fin g → ℂ} (hv : ∀ k ∈ S, v k = 0) :
    (fun i : {k // k ∉ S} => (τ *ᵥ v) i) =
      τ.submatrix Subtype.val Subtype.val *ᵥ (fun i : {k // k ∉ S} => v i) := by
  funext i
  simp only [mulVec, submatrix_apply]
  rw [dotProduct_comm, dotProduct_eq_restrict_of_vanishing S hv, dotProduct_comm]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem thetaCharOff_eq_theta_submatrix (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ)
    (c₁ c₂ : Fin g → ℂ) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hS : ∀ k ∈ S, c₁ k = 0) (z : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ z = _root_.ReciprocityTheory.PTheta.theta (fun i : {k // k ∉ S} => (c₁ i).re)
      (fun i : {k // k ∉ S} => (c₂ i).re) (fun i : {k // k ∉ S} => z i)
      (τ.submatrix Subtype.val Subtype.val) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff _root_.ReciprocityTheory.PTheta.theta _root_.ReciprocityTheory.PTheta.thetaTerm _root_.ReciprocityTheory.PTheta.eC _root_.ReciprocityTheory.PTheta.shiftVec _root_.ReciprocityTheory.PTheta.ofRealVec
  rw [← (_root_.GlobalTheory.ThetaBlock.offEquiv S).tsum_eq]
  congr 1
  funext n
  have hv : ∀ k ∈ S, ((fun i => ((n.1 i : ℤ) : ℂ)) + c₁) k = 0 := fun k hk => by
    simp [n.2 k hk, hS k hk]
  have hw : (fun i : {k // k ∉ S} =>
      (((_root_.GlobalTheory.ThetaBlock.offEquiv S n) i : ℤ) : ℂ) + (((c₁ i).re : ℝ) : ℂ)) =
      fun i : {k // k ∉ S} => ((fun i => ((n.1 i : ℤ) : ℂ)) + c₁) i := by
    funext i
    rw [ofReal_re_eq_self_of_eq_zero_or_half (h₁ i)]
    rfl
  have hz : (fun i : {k // k ∉ S} => z i) + (fun i : {k // k ∉ S} => (((c₂ i).re : ℝ) : ℂ)) =
      fun i : {k // k ∉ S} => (z + c₂) i := by
    funext i
    simp [ofReal_re_eq_self_of_eq_zero_or_half (h₂ i)]
  rw [hw, hz, dotProduct_eq_restrict_of_vanishing S hv (τ *ᵥ _), mulVec_restrict_eq_submatrix_mulVec_of_vanishing S τ hv,
    dotProduct_eq_restrict_of_vanishing S hv (z + c₂)]
  congr 1
  ring

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in

theorem _root_.GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic (g : ℕ) (S : Finset (Fin g))
    (τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2)
    (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) (hS : ∀ k ∈ S, c₁ k = 0) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ ≠ 0 ∧ Differentiable ℂ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂) ∧
      ∀ m n : Fin g → ℤ, (∀ k ∈ S, n k = 0) → ∃ a : ℂ, a ≠ 0 ∧ ∀ z,
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) =
          a * Complex.exp (-(2 * Real.pi * Complex.I) * ((fun i => (n i : ℂ)) ⬝ᵥ z)) *
            _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ z := by
  have hτ := submatrix_mem_siegelH_of_posDef_im S hs hp
  have hfun : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ = fun z => _root_.ReciprocityTheory.PTheta.theta (fun i : {k // k ∉ S} => (c₁ i).re)
      (fun i : {k // k ∉ S} => (c₂ i).re) (fun i : {k // k ∉ S} => z i)
      (τ.submatrix Subtype.val Subtype.val) :=
    funext (thetaCharOff_eq_theta_submatrix S τ c₁ c₂ h₁ h₂ hS)
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    obtain ⟨w, hw⟩ := Function.ne_iff.1
      (_root_.GlobalTheory.theta_ne_zero hτ (fun i : {k // k ∉ S} => (c₁ i).re)
        (fun i : {k // k ∉ S} => (c₂ i).re))
    apply hw
    have h := congrFun h0 (fun k => if h : k ∈ S then 0 else w ⟨k, h⟩)
    rw [hfun] at h
    have hr : (fun i : {k // k ∉ S} => (fun k => if h : k ∈ S then 0 else w ⟨k, h⟩) i.1) = w := by
      funext i
      simp [i.2]
    simp only [Pi.zero_apply] at h
    rwa [hr] at h
  · rw [hfun]
    exact (_root_.GlobalTheory.differentiable_theta hτ _ _).comp (by fun_prop)
  · intro m n hn
    set N : Fin g → ℂ := fun i => (n i : ℂ) with hN
    set M : Fin g → ℂ := fun i => (m i : ℂ) with hM
    have hsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ τ *ᵥ y = y ⬝ᵥ τ *ᵥ x := by
      intro x y
      rw [dotProduct_mulVec, ← mulVec_transpose, hs.eq, dotProduct_comm]
    refine ⟨Complex.exp (2 * Real.pi * Complex.I * (c₁ ⬝ᵥ M) -
      Real.pi * Complex.I * (N ⬝ᵥ τ *ᵥ N) - 2 * Real.pi * Complex.I * (N ⬝ᵥ c₂)),
      Complex.exp_ne_zero _, fun z => ?_⟩
    let e : {p : Fin g → ℤ // ∀ k ∈ S, p k = 0} ≃ {p : Fin g → ℤ // ∀ k ∈ S, p k = 0} :=
      { toFun := fun p => ⟨p.1 - n, fun k hk => by simp [p.2 k hk, hn k hk]⟩
        invFun := fun p => ⟨p.1 + n, fun k hk => by simp [p.2 k hk, hn k hk]⟩
        left_inv := fun p => by ext; simp
        right_inv := fun p => by ext; simp }
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff
    rw [← e.tsum_eq, ← tsum_mul_left]
    congr 1
    funext p
    have hQ : (fun i => (((e p).1 i : ℤ) : ℂ)) = (fun i => ((p.1 i : ℤ) : ℂ)) - N := by
      funext i
      simp [e, hN]
    rw [hQ, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨∑ i, (p.1 i - n i) * m i, ?_⟩
    have hcast : ((∑ i, (p.1 i - n i) * m i : ℤ) : ℂ) =
        (fun i => ((p.1 i : ℤ) : ℂ)) ⬝ᵥ M - N ⬝ᵥ M := by
      simp [dotProduct, hM, hN, Finset.sum_sub_distrib, sub_mul]
    simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, mulVec_add,
      mulVec_sub]
    linear_combination (Real.pi * Complex.I) * hsym (fun i => ((p.1 i : ℤ) : ℂ)) N +
      (Real.pi * Complex.I) * hsym c₁ N - (2 * Real.pi * Complex.I) * hcast

end GlobalTheory.ThetaBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSumShift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem isFShift_iff {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (k : ℕ) [NeZero k] (α : A.X)
    (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) (F : ℂ⸨X⸩)
    (hd : (k : ℤ) ∣ A.be la.y α := by apply_assumption) :
    IsFShift A k α th la z F ↔ F = A.FSumShift k α th la z := by
  have key : ∀ n : ℤ, (∑ᶠ (m : A.X) (_ : A.exponent k (α + la.y) m + A.be la.y α / k = n),
      A.term k α th m (z + (k : ℂ)⁻¹ • A.P0 la)) = (A.FSumShift k α th la z).coeff n := fun n => by
    rw [AnArc.coeff_FSumShift]
    refine finsum_cond_eq_sum_of_cond_iff _ fun {m} _ => ?_
    rw [AnArc.mem_level, eq_sub_iff_add_eq]
  unfold IsFShift
  simp only [key]
  exact ⟨fun h => HahnSeries.ext (funext h.2), fun h => ⟨⟨NeZero.ne k, hd⟩, fun n => by rw [h]⟩⟩

theorem theta_sum_shift : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∀ (k : ℕ) [NeZero k] (la : A.La), (∀ α, (k : ℤ) ∣ A.be la.y α) → ∃ cz : A.V → ℂ, (∀ z, cz z ≠ 0) ∧ ∀ α, ∀ th ∈ A.Theta k α, ∃ th' ∈ A.Theta k (α + la.y), (th ≠ 0 → th' ≠ 0) ∧ ∀ z, (∀ F, IsFShift A k α th la z F ↔ F = HahnSeries.single (A.be la.y α / k) (cz z) * A.FSum k (α + la.y) th' z) ∧ ∀ w : ℂ, A.Sum k α th w (z + (k : ℂ)⁻¹ • A.Pw w la) = cz z * eTwoPi (w * ((A.be la.y α / k : ℤ) : ℂ)) * A.Sum k (α + la.y) th' w z := by
  intro O _ _ A k _ la hla
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  refine ⟨fun z => Complex.exp (A.lin la z), fun z => Complex.exp_ne_zero _, fun α th hth =>
    ⟨A.shift k la α th, A.shift_mem_Theta hth la, fun h h' => h ?_, fun z => ⟨fun F => ?_, fun w => ?_⟩⟩⟩
  · exact A.shift_injective k la α (h'.trans (map_zero _).symm)
  · rw [isFShift_iff A k α th la z F (hla α), A.FSumShift_eq k la (Int.mul_ediv_cancel' (hla α)).symm]
  · obtain ⟨m, hm⟩ := hla α
    rw [A.Sum_add_Pw_div, hm, Int.mul_ediv_cancel_left _ (NeZero.ne (k : ℤ))]
    congr 3
    push_cast
    field_simp

end GlobalTheory.ArcPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusCoordinateRatioDifferentiableAtOrigin
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
open Filter Topology

namespace GlobalTheory.AbelianLetters

theorem exists_top_le_wchart {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Sp ℂ ⟶ X)) : ∃ j, ⊤ ≤ LB.wchart L φ j := by
  choose j hj using fun k => exists_chart hL (φ k (default : PrimeSpectrum ℂ))
  refine ⟨j, fun p _ => Set.mem_iInter.2 fun k => ?_⟩
  obtain rfl : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hj k

theorem valAt'_unit_ne_zero {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    valAt' x U f.val ≠ 0 := by
  rw [HolHom.valAt'_eq_valR, HolHom.valR_eq _ _ h]
  exact (f.isUnit.map _).ne_zero

theorem IsRatio.differentiableAt_zero : ∀ [Algebra (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (s₀ : Out.GtPt D D.P.A), s₀.b = 𝟙 D.P.A ^ n → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n s₀ u → ∀ x, DifferentiableAt ℂ (u x) 0 := by
  intro _ D g n ex s₀ hb hadd hol hchi u hu x
  obtain ⟨j, hj⟩ := exists_top_le_wchart D.P.isLB (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • 0)).b x)
  have h1 : ∀ z, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j ↔
      ⊤ ≤ (show Sp ℂ ⟶ _ from (ex z).b.left) ⁻¹ᵁ LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A (𝟙 D.P.A ^ 1) x) j := by
    intro z
    have := top_le_wchart_nsmul hadd (n := 1) rfl z x j
    rwa [Nat.cast_one, one_smul] at this
  have hS : {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j} ∈ 𝓝 ((n : ℂ) • (0 : Fin g → ℂ)) := by
    filter_upwards [(HolHom.holAt_of_isHolTo hol (Set.mem_univ ((n : ℂ) • (0 : Fin g → ℂ))) _ ((h1 _).1 hj)).1]
      with t ht using (h1 t).2 ht
  have hn : DifferentiableAt ℂ (fun z : Fin g → ℂ => (n : ℂ) • z) 0 := by fun_prop
  have hc : DifferentiableAt ℂ (fun z => chiVal (ex ((n : ℂ) • z)) x j) 0 :=
    ((hchi x j).differentiableAt hS).comp 0 hn
  have h0 := (top_le_wchart_nsmul hadd hb 0 x j).1 hj
  obtain ⟨hev, hd⟩ := HolHom.holAt_of_isHolTo hol (Set.mem_univ 0) _ h0
  refine (hc.fun_mul ((hd ((s₀.s x).s j).val).fun_inv (valAt'_unit_ne_zero _ h0 _))).congr_of_eventuallyEq ?_
  filter_upwards [hev] with t ht
  exact (eq_mul_inv_iff_mul_eq₀ (valAt'_unit_ne_zero _ ht _)).2
    (hu x t j ((top_le_wchart_nsmul hadd hb t x j).2 ht)).symm

end GlobalTheory.AbelianLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusCoordinateRatioEqTorusCoordOverOrigin
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor CategoryTheory.MonObj GlobalTheory.AbelianLetters

namespace GlobalTheory.AbelianLetters.TorusRatio

theorem valR_of_corr_one {A : Type} [CommRing A] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {ε : K → ℤ}
    {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (h : LB.Gen.Corr L _ _ _ _ t (LB.oneGen L))
    (x : Sp A ⟶ Y) (j : K → L.ι) (hj : LB.Coh L φ j) (hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j) :
    valR x (LB.wchart L φ j) (t.s j).val = 1 := by
  have e := h j PEmpty.elim hj (fun k => k.elim) (fun _ k => k.elim)
  have hx' : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim) :=
    fun y hy => ⟨hx hy, Set.mem_iInter.2 fun k => k.elim⟩
  have e1 : res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim ≤ _)
      (t.s j) = 1 := e.trans (map_one _)
  refine (HolHom.valR_res x inf_le_left _ hx').symm.trans ?_
  refine (congrArg (fun q => valR x _ q.val) e1).trans ?_
  exact (HolHom.valR_eq x _ hx' _).trans (map_one _)

theorem isZero_of_isAdd {R : Type} [CommRing R] [IsDomain R] {D : Out.DegPre R} {T : Over (Sp R)}
    {g : Out.GtPt D T} (hb : g.b = 1) (h : Out.GtPt.IsAdd g g g) (χ : D.X) :
    LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L) := by
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    ((val_corr hJ (h.2 χ) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c1 : TorusCoord.cubVal (𝟙 _ ≫ (lift (Out.DegPre.cT D T χ) (lift g.b g.b)).left) y J = 1 := by
    rw [Category.id_comp, hb]
    exact (isCub_cubV D.cub hJ).face₂ _ _
  have e2 := (congrArg (val (g.s χ) (𝟙 _) y J * ·) c1).symm.trans e
  rw [_root_.mul_one] at e2
  exact (mul_eq_left.1 e2.symm).trans (val_one _).symm

theorem ratio_eq_torus_coord [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ)
    (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt)
    (hb : ∀ Tt b, (sB Tt b).b = b ^ n)
    (hadd : ∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b')))
    (hpull : ∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b)))
    (hex : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) :
    (∀ p : Out.GtPtF D ℂ, p.IsZero → IsTorusPt p (fun _ => 1)) ∧
      ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → ∀ (z : Fin g → ℂ) (xv : D.X → ℂ),
        (ex z).b = Out.DegPre.zeroF D ℂ → IsTorusPt (ex ((n : ℂ) • z)) xv → ∀ x, u x z = xv x := by
  refine ⟨fun p hp => ⟨hp.1, fun χ j hj hc => valR_of_corr_one (hp.2 χ) (𝟙 (Sp ℂ)) j hj hc⟩,
    fun u hu z xv hz ht x => ?_⟩
  have hz1 : (ex z).b = 1 := hz
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (Z := Sp ℂ) (IsLocalRing.closedPoint ℂ)
  have hs : (sB (Out.TF (R := ℂ) ℂ) 1).b = (ex ((n : ℂ) • z)).b := by
    rw [hb, b_nsmul hex, hz1]
  let j : Fin 4 → D.P.L.ι := fun k => J (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x k)
  have hj : LB.Coh D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j := fun _ _ e => congrArg J e
  have hc : ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x) j := fun y _ =>
    Set.mem_iInter.2 fun k => by
      obtain rfl : y = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      exact hJ _
  have h1 := hu x z j hc
  rw [ht.2 x j hj hc] at h1
  have hp := hpull D.P.A (Out.TF (R := ℂ) ℂ) (ex z).b (𝟙 _)
  have ha := hadd (Out.TF (R := ℂ) ℂ) 1 1
  rw [_root_.mul_one] at ha
  have e1 : (ex z).b ≫ 𝟙 D.P.A = 1 := (Category.comp_id _).trans hz1
  rw [e1] at hp
  have h2 := valR_of_isPull (A := ℂ) (p := (Out.TF (R := ℂ) ℂ).hom) hp x j
  have h3 := valR_of_corr_one (isZero_of_isAdd ((hb _ _).trans (one_pow n)) ha x) (𝟙 (Sp ℂ)) j
    (by rw [hs]; exact hj) (by rw [hs]; exact hc)
  have h4 := h2.symm.trans h3
  exact ((congrArg (u x z * ·) h4).trans (_root_.mul_one _)).symm.trans h1.symm

end GlobalTheory.AbelianLetters.TorusRatio
end
end

