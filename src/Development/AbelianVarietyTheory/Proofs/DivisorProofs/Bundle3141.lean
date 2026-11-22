import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSpanVanishingEqUniformiserMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ModPi

theorem gp_comp_cst (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (GlobalTheory.Desc.cst p) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, gp,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.Desc.cst, fnOf, Scheme.functionField]

theorem cst_reg_zero (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X)
    (hx : p x = closedPoint R) (r : R) :
    GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) ∧ (r ∈ maximalIdeal R → GlobalTheory.Cartier.ZeroAt x (GlobalTheory.Desc.cst p r)) := by
  have hreg : GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine ⟨hreg, fun hr => zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

theorem span_add {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁) {S : Set F₁} {v w : F₁}
    (hv : v ∈ spanBy c S) (hw : w ∈ spanBy c S) : v + w ∈ spanBy c S := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  obtain ⟨m, r', t', ht', rfl⟩ := hw
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ht i
    · rw [Fin.append_right]; exact ht' i
  · rw [Fin.sum_univ_add]; simp

theorem regAt_npow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : GlobalTheory.Cartier.RegAt x f) (n : ℕ) :
    GlobalTheory.Cartier.RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem modPi : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ ϖ : T, maximalIdeal T = Ideal.span {ϖ} → ∀ z ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), GlobalTheory.Cartier.ZeroAt y' z → ∃ z₁ ∈ spanBy (GlobalTheory.Desc.cst H'.hom) (θ '' regSet y), z = GlobalTheory.Desc.cst H'.hom (a ϖ) * z₁ := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hff y y' hy hy' hdy hdy' ϖ hmT
  have hmD : maximalIdeal D = Ideal.span {a ϖ} := by rw [← hm, hmT, Ideal.map_span, Set.image_singleton]
  have hcomp : θ.comp (cst H.hom) = (cst H'.hom).comp a := by
    obtain ⟨l, hl1, hl2⟩ := hff
    have e1 := gp_comp_cst H.left T H.hom
    have e2 := gp_comp_cst H'.left D H'.hom
    have hl : l = gp H'.left := by simpa using hl1
    have key : spMap (θ.comp (cst H.hom)) = spMap ((cst H'.hom).comp a) := by
      calc spMap (θ.comp (cst H.hom)) = spMap θ ≫ spMap (cst H.hom) := by simp [spMap, CommRingCat.ofHom_comp]
        _ = spMap θ ≫ gp H.left ≫ H.hom := by rw [e1]
        _ = l ≫ π ≫ H.hom := by rw [← Category.assoc, ← hl2, Category.assoc]
        _ = gp H'.left ≫ H'.hom ≫ spMap a := by rw [hpb.w, hl]
        _ = spMap (cst H'.hom) ≫ spMap a := by rw [← Category.assoc, e2]
        _ = spMap ((cst H'.hom).comp a) := by simp [spMap, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  have hθc : ∀ t, θ (cst H.hom t) = cst H'.hom (a t) := fun t => by
    rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply]
  set c := cst H'.hom with hc
  have hreg : ∀ u, GlobalTheory.Cartier.RegAt y u → GlobalTheory.Cartier.RegAt y' (θ u) := by
    intro u hu
    have hpt := GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy'
    exact GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp H.left H'.left π θ ⟨_, hff.choose_spec⟩ y' u (hpt ▸ hu)
  have hcreg : ∀ d, GlobalTheory.Cartier.RegAt y' (c d) := fun d => (cst_reg_zero D H'.left H'.hom y' hy' d).1
  have hc0reg : ∀ t, GlobalTheory.Cartier.RegAt y (cst H.hom t) := fun t => (cst_reg_zero T H.left H.hom y hy t).1
  have hϖz : GlobalTheory.Cartier.ZeroAt y (cst H.hom ϖ) :=
    (cst_reg_zero T H.left H.hom y hy ϖ).2 (by rw [hmT]; exact Ideal.subset_span rfl)
  obtain ⟨hϖ0, hfac⟩ := GlobalTheory.T.semiAbelian_dvr_closedFibre_stalk_uniformiser T H hH y hy hdy ϖ hmT

  have hdiv : ∀ x, GlobalTheory.Cartier.ZeroAt y x → ∃ w, GlobalTheory.Cartier.RegAt y w ∧ x = cst H.hom ϖ * w := by
    intro x hx
    by_cases hx0 : x = 0
    · exact ⟨0, regAt_zero y, by rw [hx0, mul_zero]⟩
    obtain ⟨k, w, hw, rfl⟩ := hfac x hx0
    rcases le_or_gt 1 k with hk | hk
    · refine ⟨cst H.hom ϖ ^ (k - 1).toNat * w, (regAt_npow (hc0reg ϖ) _).mul hw.regAt, ?_⟩
      rw [← _root_.mul_assoc, ← pow_succ', ← zpow_natCast]
      congr 2; omega
    · exfalso
      have hk' : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have e : cst H.hom ϖ ^ k * w * cst H.hom ϖ ^ (-k).toNat = w := by
        rw [mul_comm _ (cst H.hom ϖ ^ (-k).toNat), ← _root_.mul_assoc, ← zpow_natCast, hk',
          ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, _root_.one_mul]
      exact (zeroAt_iff.1 (e ▸ hx.mul (regAt_npow (hc0reg ϖ) _))).2 hw
  have hgeo := GlobalTheory.T.residueField_linearIndependent_closedFibre_genericPoints T D a ha hm H H' π θ hH hpb hff y y' hy hy' hdy hdy'
  set S := spanBy c (θ '' regSet y) with hS

  have hyes : ∀ (n : ℕ) (d : Fin n → D) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) →
      (∀ cc : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, cst H.hom (cc i) * u i) → ∀ i, cc i ∈ maximalIdeal T) →
      GlobalTheory.Cartier.ZeroAt y' (∑ i, c (d i) * θ (u i)) → ∃ z₁ ∈ S, ∑ i, c (d i) * θ (u i) = c (a ϖ) * z₁ := by
    intro n d u hu hind hz
    have hd := hgeo n u hu hind d hz
    choose e he using fun i => Ideal.mem_span_singleton'.1 (hmD ▸ hd i)
    refine ⟨∑ i, c (e i) * θ (u i), ⟨n, e, fun i => θ (u i), fun i => ⟨u i, hu i, rfl⟩, rfl⟩, ?_⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← he i, map_mul]; ring
  have hmain : ∀ (n : ℕ) (d : Fin n → D) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) →
      GlobalTheory.Cartier.ZeroAt y' (∑ i, c (d i) * θ (u i)) → ∃ z₁ ∈ S, ∑ i, c (d i) * θ (u i) = c (a ϖ) * z₁ := by
    intro n
    induction n with
    | zero => intro d u hu hz; exact hyes 0 d u hu (fun _ _ i => i.elim0) hz
    | succ n ih =>
      intro d u hu hz
      by_cases hind : ∀ cc : Fin (n + 1) → T, GlobalTheory.Cartier.ZeroAt y (∑ i, cst H.hom (cc i) * u i) → ∀ i, cc i ∈ maximalIdeal T
      · exact hyes _ d u hu hind hz
      push_neg at hind
      obtain ⟨cc, hZ, k, hk⟩ := hind
      obtain ⟨ν, hν⟩ : ∃ ν : T, ν * cc k = 1 := by
        obtain ⟨v, hv⟩ := IsLocalRing.notMem_maximalIdeal.1 hk
        exact ⟨↑v⁻¹, by rw [← hv, Units.inv_mul]⟩
      obtain ⟨w, hw, hrel⟩ := hdiv _ hZ
      rw [Fin.sum_univ_succAbove _ k] at hrel
      have hrel' := congrArg θ hrel
      simp only [map_add, map_sum, map_mul, hθc] at hrel'
      have hν' : c (a ν) * c (a (cc k)) = 1 := by rw [← map_mul, ← map_mul, hν, map_one, map_one]
      set d' : Fin n → D := fun j => d (k.succAbove j) - d k * a ν * a (cc (k.succAbove j)) with hd'
      set u' : Fin n → H.left.functionField := fun j => u (k.succAbove j) with hu'
      have hsplit : ∑ i, c (d i) * θ (u i) = c (a ϖ) * (c (d k * a ν) * θ w) + ∑ j, c (d' j) * θ (u' j) := by
        rw [Fin.sum_univ_succAbove _ k]
        have : ∑ j, c (d' j) * θ (u' j) = ∑ j, c (d (k.succAbove j)) * θ (u (k.succAbove j)) -
            c (d k) * c (a ν) * ∑ j, c (a (cc (k.succAbove j))) * θ (u (k.succAbove j)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hd', hu', map_sub, map_mul]; ring
        rw [this, map_mul]
        linear_combination (c (d k) * c (a ν)) * hrel' - (c (d k) * θ (u k)) * hν'
      have hz' : GlobalTheory.Cartier.ZeroAt y' (∑ j, c (d' j) * θ (u' j)) := by
        have e : ∑ j, c (d' j) * θ (u' j) = ∑ i, c (d i) * θ (u i) + c (a ϖ) * (c (-(d k * a ν)) * θ w) := by
          rw [hsplit, map_neg]; ring
        rw [e]
        refine hz.add (ZeroAt.mul ?_ ((hcreg _).mul (hreg w hw)))
        exact (cst_reg_zero D H'.left H'.hom y' hy' (a ϖ)).2 (by rw [hmD]; exact Ideal.subset_span rfl)
      obtain ⟨z₁, hz₁, e₁⟩ := ih d' u' (fun j => hu _) hz'
      refine ⟨c (d k * a ν) * θ w + z₁, span_add c ⟨1, fun _ => d k * a ν, fun _ => θ w, fun _ => ⟨w, hw, rfl⟩, by simp⟩ hz₁, ?_⟩
      rw [hsplit, e₁]; ring
  intro z hz hzy
  obtain ⟨n, r, t, ht, rfl⟩ := hz
  choose u hu hut using ht
  have e : ∑ i, c (r i) * t i = ∑ i, c (r i) * θ (u i) := Finset.sum_congr rfl fun i _ => by rw [hut i]
  rw [e] at hzy ⊢
  exact hmain n r u hu hzy

end GlobalTheory.Desc.ModPi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
namespace GlobalTheory.ProdUnif

open GlobalTheory.WCub GlobalTheory.PowUnif

set_option maxHeartbeats 1600000 in

theorem cubAlong_prod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (L : LB (G₁ ⊗ G₂).left) (c : CubGen (G₁ ⊗ G₂) L) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → IsBoxGen (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (φ₁ := thφ D₁.toPre.P.A (x3 D₁.toPre.P.A)) (φ₂ := thφ D₂.toPre.P.A (x3 D₂.toPre.P.A)) (ε := thε) wM (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.toPre.cub.t D₁.toPre.cub.t D₂.toPre.cub.t → IsBoxGen (φ₁ := thφ G₁ (x3 G₁)) (φ₂ := thφ G₂ (x3 G₂)) wL (fst G₁ G₂ ⊗ₘ fst G₁ G₂ ⊗ₘ fst G₁ G₂).left (snd G₁ G₂ ⊗ₘ snd G₁ G₂ ⊗ₘ snd G₁ G₂).left c U₁.cubG.t U₂.cubG.t → ∀ (e : ℕ) (g : GtCoord I D.toPre e (G₁ ⊗ G₂)), g.pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → g.pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → ∀ w : LB.Iso (L.pull (fstG I e (G₁ ⊗ G₂)).left) (D.toPre.P.L.pull g.pG.left), BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL w (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → CubAlong I D.toPre e (G₁ ⊗ G₂) L c g.pG w := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D p₁ p₂ q₁ q₂ hS wM L c wL hLB hM hL e g h₁ h₂ w hQ T x jL jM cL cM
  have := g.q_hom
  have := (U₁.gt e).q_hom
  have := (U₂.gt e).q_hom
  have := hS.hom₁
  have := hS.hom₂
  refine (clause_iff (tri (thick R I e) g.pG x) (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x)
    (fun k : thK => (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left) _ _ _ (D.toPre.cub.t.s jM) (c.s jL)
    (fun k => w.s (fun _ => jM k, fun _ => jL k)) thε).2 fun y hB hG' _ => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ jM cM (fun k => Set.mem_iInter.1 hB k)
  obtain ⟨N, hN, eN⟩ := exists_good L hLB y _ jL cL (fun k => Set.mem_iInter.1 hG' k)
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.toPre.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.toPre.P.isLB y
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.BoxFamily.exists_good_at U₁.LG.isLB y
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.BoxFamily.exists_good_at U₂.LG.isLB y
  have tM₁ := (tri_map (thick R I e) (U₁.gt e).pG g.pG x _ p₁ h₁).2
  have tM₂ := (tri_map (thick R I e) (U₂.gt e).pG g.pG x _ p₂ h₂).2
  have tL₁ := (tri_map (thick R I e) (fstG I e G₁) (fstG I e (G₁ ⊗ G₂)) x _ (fst G₁ G₂)
    (thick_fstG I e (fst G₁ G₂))).2
  have tL₂ := (tri_map (thick R I e) (fstG I e G₂) (fstG I e (G₁ ⊗ G₂)) x _ (snd G₁ G₂)
    (thick_fstG I e (snd G₁ G₂))).2
  have bM := hM T.left (tri (thick R I e) g.pG x) y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [tM₁, tM₂] at bM
  have bL := hL T.left (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x) y N₁ N₂ N hN₁ hN₂ hN
  rw [tL₁, tL₂] at bL
  have v₁ := w_cub_val.{0} U₁ e T (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) y hJ₁ hN₁
  have v₂ := w_cub_val.{0} U₂ e T (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) y hJ₂ hN₂

  have fM := fun k : thK => tri_thφ (thick R I e) g.pG x g.q rfl k
  have fG := fun k : thK => tri_thφ (thick R I e) (fstG I e (G₁ ⊗ G₂)) x (𝟙 _) (Category.id_comp _).symm k
  have fM₁ := fun k : thK => tri_thφ (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) (U₁.gt e).q rfl k
  have fM₂ := fun k : thK => tri_thφ (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) (U₂.gt e).q rfl k
  have fG₁ := fun k : thK => tri_thφ (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) (𝟙 _)
    (Category.id_comp _).symm k
  have fG₂ := fun k : thK => tri_thφ (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) (𝟙 _)
    (Category.id_comp _).symm k
  have ps₁ := fun k : thK => psum_comp x ((Over.pullback (thick R I e)).map (fst G₁ G₂)) k.down
  have ps₂ := fun k : thK => psum_comp x ((Over.pullback (thick R I e)).map (snd G₁ G₂)) k.down
  have key := rel_alg thε
    (fun k => om wM y J₁ J₂ J (tri (thick R I e) g.pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k))
    (fun k => om wL y N₁ N₂ N (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x ≫ thφ (G₁ ⊗ G₂) (x3 (G₁ ⊗ G₂)) k))
    (fun k => gw w (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left y (jM k) (fun _ => jL k))
    (fun k => gw (U₁.w e) (psum (thickObj R I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) k.down).left y
      (J₁ (tri (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ D₁.toPre.P.A (x3 D₁.toPre.P.A) k))
      (fun _ => N₁ (tri (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ G₁ (x3 G₁) k)))
    (fun k => gw (U₂.w e) (psum (thickObj R I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) k.down).left y
      (J₂ (tri (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ D₂.toPre.P.A (x3 D₂.toPre.P.A) k))
      (fun _ => N₂ (tri (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ G₂ (x3 G₂) k)))
    (fun k => by
      have q := hQ T.left (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      have a₁ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ g.pG.left) ≫ p₁.left =
          tri (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ D₁.toPre.P.A (x3 D₁.toPre.P.A) k := by
        rw [Category.assoc, h₁, ← Category.assoc, ps₁ k, fM₁ k]
      have a₂ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ g.pG.left) ≫ p₂.left =
          tri (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ D₂.toPre.P.A (x3 D₂.toPre.P.A) k := by
        rw [Category.assoc, h₂, ← Category.assoc, ps₂ k, fM₂ k]
      have b₁ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ (fstG I e (G₁ ⊗ G₂)).left) ≫ (fst G₁ G₂).left =
          tri (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ G₁ (x3 G₁) k := by
        rw [Category.assoc, thick_fstG I e (fst G₁ G₂), ← Category.assoc, ps₁ k, fG₁ k]
      have b₂ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ (fstG I e (G₁ ⊗ G₂)).left) ≫ (snd G₁ G₂).left =
          tri (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ G₂ (x3 G₂) k := by
        rw [Category.assoc, thick_fstG I e (snd G₁ G₂), ← Category.assoc, ps₂ k, fG₂ k]
      rw [a₁, a₂, b₁, b₂, ps₁ k, ps₂ k, ← fM k, ← fG k, eJ k, eN k] at q
      exact q)
    bM bL v₁ v₂
  refine (val_of _ _ y J jM eJ).symm.trans (key.trans ?_)
  exact congrArg _ (val_of c _ y N jL eN)

end GlobalTheory.ProdUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerCechH1Uniform
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg.TowerH1
variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}

theorem cst_eq_zero (e : ℕ) (V : (Y e).left.Opens) {a : R} (ha : a ∈ I ^ (e + 1)) :
    AbLaw.cst ((Y e).hom ≫ thick R I e) V a = 0 := by
  have h : (thick R I e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = 0 := by
    have := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← this]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  simp only [AbLaw.cst, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, h, map_zero]

theorem mul_eq_zero_of_mem (e : ℕ) (V : (Y e).left.Opens) {x y : Γ((Y e).left, V)}
    (hx : x ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) : x * y = 0 := by
  have h : x * y ∈ towerIdeal Y e (I ^ (e + 1)) V := by
    have h0 := Ideal.mul_mem_mul hx hy
    unfold towerIdeal at h0 ⊢
    rw [← Ideal.map_mul, ← pow_succ'] at h0
    exact h0
  have hb : towerIdeal Y e (I ^ (e + 1)) V = ⊥ := by
    unfold towerIdeal
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    exact cst_eq_zero e V ha
  rw [hb] at h
  exact h

theorem mul_eq_mul_of_sub_mem (e : ℕ) (V : (Y e).left.Opens) {x x' y : Γ((Y e).left, V)}
    (hx : x - x' ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) : x * y = x' * y := by
  have := mul_eq_zero_of_mem e V hx hy
  rw [sub_mul] at this
  exact sub_eq_zero.1 this

theorem pow_mul_eq_pow_mul_of_sub_mem (e : ℕ) (V : (Y e).left.Opens) {x x' y : Γ((Y e).left, V)}
    (hx : x - x' ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) (m : ℕ) :
    x ^ m * y = x' ^ m * y :=
  mul_eq_mul_of_sub_mem e V (Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow x x' m) hx) hy

theorem pow_mul_eq_of_sub_one_mem (e : ℕ) (V : (Y e).left.Opens) {x y : Γ((Y e).left, V)}
    (hx : x - 1 ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) (m : ℕ) : x ^ m * y = y := by
  rw [pow_mul_eq_pow_mul_of_sub_mem e V hx hy m, one_pow, one_mul]

theorem rs_mem (e : ℕ) (J : Ideal R) {U V : (Y e).left.Opens} (h : V ≤ U) {x : Γ((Y e).left, U)}
    (hx : x ∈ towerIdeal Y e J U) : rs (Y e).left h x ∈ towerIdeal Y e J V := by
  unfold towerIdeal at hx ⊢
  have h1 := Ideal.mem_map_of_mem (rs (Y e).left h) hx
  rw [Ideal.map_map] at h1
  have h2 : (rs (Y e).left h).comp (AbLaw.cst ((Y e).hom ≫ thick R I e) U) = AbLaw.cst ((Y e).hom ≫ thick R I e) V :=
    RingHom.ext fun r => rs_cst _ h r
  rwa [h2] at h1

theorem isUnit_rs_of_le_basicOpen {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U))
    (hb : V ≤ X.basicOpen f) : IsUnit (rs X h f) := by
  have hu : IsUnit (rs X (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  have := hu.map (rs X hb)
  rwa [rs_rs] at this

end GlobalTheory.FormalAlg.TowerH1

namespace GlobalTheory.FormalAlg.TowerH1

theorem ev_X {R : Type} [CommRing R] {I : Ideal R}
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ} (C : Charts I Y β n) (e : ℕ) (i m : Fin (n + 1)) :
    C.ev e i (MvPolynomial.X m) = C.ρ e i m := by
  simp only [Charts.ev, MvPolynomial.eval₂Hom_X']

end GlobalTheory.FormalAlg.TowerH1

open GlobalTheory.FormalAlg.TowerH1 in

theorem GlobalTheory.FormalAlg.towerCech_h1_uniform : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ e : ℕ, (∀ c : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j), (∀ i j, c i j ∈ towerIdeal Y e (I ^ e) _) → (∀ i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e j) (c i j) + rs (Y e).left (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) (C.ρ e i j) ^ k * rs (Y e).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j ⊓ C.D e l) (c j l) = rs (Y e).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e l) (c i l)) → ∃ a : ∀ i, Γ((Y e).left, C.D e i), (∀ i, a i ∈ towerIdeal Y e (I ^ e) _) ∧ ∀ i j, c i j = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (a i) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (a j)) := by
  intro R _ _ I Y β hβ n C
  classical
  let J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R) := fun e => ⨅ i, RingHom.ker (C.ev e i)
  have hJ : ∀ e F, F ∈ J e ↔ ∀ i, C.ev e i F = 0 := by
    intro e F
    simp only [J, Ideal.mem_iInf, RingHom.mem_ker]
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.uniform_serre_vanishing_cech_cocycles R I n J (fun e t a F ha _ _ hF =>
    (hJ _ _).2 fun i => GlobalTheory.T.liftedRatios_eval_ideal_mul_eq_zero_succ R I Y β hβ n C e a F i ha ((hJ e F).1 hF i))
  refine ⟨d₀, fun k hk e c hc hcoc => ?_⟩
  have lev := GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C
  choose N₀ hN₀ using fun i j => GlobalTheory.T.exists_homogeneous_form_of_overlap_ideal_pow_thickening R I Y β hβ n C e i j (c i j) (hc i j)
  let N := Finset.univ.sup (fun p : Fin (n + 1) × Fin (n + 1) => N₀ p.1 p.2)
  have hN : ∀ i j, N₀ i j ≤ N := fun i j =>
    Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) => N₀ p.1 p.2) (Finset.mem_univ (i, j))
  choose F hFh hFc hFe using fun i j => hN₀ i j N (hN i j) k
  have hFm : ∀ i j, F i j ∈ Ideal.map MvPolynomial.C (I ^ e) := fun i j =>
    MvPolynomial.mem_map_C_iff.2 (hFc i j)

  have htri : ∀ i j l, ∃ L : ℕ, ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * MvPolynomial.X j * MvPolynomial.X l) ^ L *
      (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l - MvPolynomial.X j ^ N * F i l) ∈ J e := by
    intro i j l
    have hH : (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l - MvPolynomial.X j ^ N * F i l :
        MvPolynomial (Fin (n + 1)) R).IsHomogeneous (N + (k + 2 * N)) :=
      (((MvPolynomial.isHomogeneous_X_pow l N).mul (hFh i j)).add
        ((MvPolynomial.isHomogeneous_X_pow i N).mul (hFh j l))).sub
        ((MvPolynomial.isHomogeneous_X_pow j N).mul (hFh i l))
    have hHc : ∀ m, MvPolynomial.coeff m (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l -
        MvPolynomial.X j ^ N * F i l : MvPolynomial (Fin (n + 1)) R) ∈ I ^ e :=
      MvPolynomial.mem_map_C_iff.1 (sub_mem (add_mem (Ideal.mul_mem_left _ _ (hFm i j))
        (Ideal.mul_mem_left _ _ (hFm j l))) (Ideal.mul_mem_left _ _ (hFm i l)))

    have hTij : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e j := inf_le_left
    have hTil : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e l := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hTjl : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j ⊓ C.D e l := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hTi : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i := inf_le_left.trans inf_le_left
    have hTj : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j := inf_le_left.trans inf_le_right
    have h1 : rs (Y e).left hTi (C.ev e i (F i j)) =
        rs (Y e).left hTi (C.ρ e i j) ^ N * rs (Y e).left hTij (c i j) := by
      have := congrArg (rs (Y e).left hTij) (hFe i j)
      simpa only [rs_rs, map_mul, map_pow] using this
    have h3 : rs (Y e).left hTi (C.ev e i (F i l)) =
        rs (Y e).left hTi (C.ρ e i l) ^ N * rs (Y e).left hTil (c i l) := by
      have := congrArg (rs (Y e).left hTil) (hFe i l)
      simpa only [rs_rs, map_mul, map_pow] using this
    have h2 : rs (Y e).left hTi (C.ev e i (F j l)) =
        rs (Y e).left hTi (C.ρ e i j) ^ (k + 2 * N) * (rs (Y e).left hTj (C.ρ e j l) ^ N *
          rs (Y e).left hTjl (c j l)) := by
      have t1 := congrArg (rs (Y e).left hTij)
        (GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hβ n C e (k + 2 * N) (F j l) (hFh j l) (hFc j l) i j).2.2
      have t2 := congrArg (rs (Y e).left hTjl) (hFe j l)
      simp only [rs_rs, map_mul, map_pow] at t1 t2
      rw [t1, t2]
    have hcjl : rs (Y e).left hTjl (c j l) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hTjl (hc j l)
    have hP : rs (Y e).left hTi (C.ρ e i i) - 1 ∈ towerIdeal Y e I _ := by
      have := rs_mem e I hTi (lev.2.1 e i)
      rwa [map_sub, map_one] at this
    have hB : rs (Y e).left hTi (C.ρ e i l) - rs (Y e).left hTi (C.ρ e i j) * rs (Y e).left hTj (C.ρ e j l)
        ∈ towerIdeal Y e I _ := by
      have := rs_mem e I hTij (lev.2.2 e i j l)
      simpa only [map_sub, map_mul, rs_rs] using this
    have e1 := pow_mul_eq_of_sub_one_mem e _ hP hcjl N
    have e2 := pow_mul_eq_pow_mul_of_sub_mem e _ hB hcjl N
    have hyp := hcoc i j l
    have hz : rs (Y e).left hTi (C.ev e i (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l -
        MvPolynomial.X j ^ N * F i l)) = 0 := by
      simp only [map_add, map_sub, map_mul, map_pow, ev_X]
      rw [h1, h2, h3]
      linear_combination (rs (Y e).left hTi (C.ρ e i j) ^ (k + 2 * N) * rs (Y e).left hTj (C.ρ e j l) ^ N) * e1 -
        rs (Y e).left hTi (C.ρ e i j) ^ (k + N) * e2 +
        rs (Y e).left hTi (C.ρ e i j) ^ N * rs (Y e).left hTi (C.ρ e i l) ^ N * hyp
    obtain ⟨L, hL⟩ := GlobalTheory.T.homogeneousForm_killed_by_power_of_tripleChart_product R I Y β hβ n C e _ _ hH hHc i j l hz
    exact ⟨L, (hJ _ _).2 hL⟩

  obtain ⟨N', G, hGh, hGc, hrel⟩ := hd₀ k hk e N F hFh hFc htri
  have tr := fun i j => GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hβ n C e (k + N') (G j) (hGh j) (hGc j) i j
  refine ⟨fun i => C.ev e i (G i), fun i => (tr i i).1, fun i j => ?_⟩
  obtain ⟨L, hL⟩ := hrel i j
  have hl : C.D e i ⊓ C.D e j ≤ C.D e i := inf_le_left
  have hr : C.D e i ⊓ C.D e j ≤ C.D e j := inf_le_right
  have h0 := congrArg (rs (Y e).left hl) ((hJ _ _).1 hL i)
  simp only [map_mul, map_sub, map_pow, ev_X, map_zero] at h0
  rw [hFe i j, (tr i j).2.2] at h0
  have hci := hc i j
  have hai : rs (Y e).left hl (C.ev e i (G i)) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hl (tr i i).1
  have haj : rs (Y e).left hr (C.ev e j (G j)) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hr (tr j j).1
  have hP : rs (Y e).left hl (C.ρ e i i) - 1 ∈ towerIdeal Y e I _ := by
    have := rs_mem e I hl (lev.2.1 e i)
    rwa [map_sub, map_one] at this
  have ec := pow_mul_eq_of_sub_one_mem e _ hP hci (L + N')
  have ea := pow_mul_eq_of_sub_one_mem e _ hP hai (L + N)
  have eb := pow_mul_eq_of_sub_one_mem e _ hP haj (L + N + N')
  have hu : IsUnit (rs (Y e).left hl (C.ρ e i j) ^ (L + N + N')) :=
    (isUnit_rs_of_le_basicOpen hl _ (lev.1 e i j).ge).pow _
  have hw : rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * (c i j - (rs (Y e).left hl (C.ev e i (G i)) -
      rs (Y e).left hl (C.ρ e i j) ^ k * rs (Y e).left hr (C.ev e j (G j)))) = 0 := by
    linear_combination h0 - rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * ec +
      rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * ea -
      rs (Y e).left hl (C.ρ e i j) ^ (L + N + N' + k) * eb
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 hw)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityHermitianFormsEqZeroOffDegree
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
namespace GlobalTheory.ChernCalc

noncomputable def linPoly {n : ℕ} (α : V n → V n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ a, ∑ b, C (α (coordVec a) (coordVec b)) * X (a, b)

theorem linPoly_isHomogeneous {n : ℕ} (α : V n → V n → ℂ) : (linPoly α).IsHomogeneous 1 := by
  unfold linPoly
  refine IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => ?_
  simpa using (isHomogeneous_C (Fin n × Fin n) (α (coordVec a) (coordVec b))).mul (isHomogeneous_X ℂ (a, b))

theorem aeval_sym_linPoly {n : ℕ} (α : V n → V n → ℂ) : aeval sym (linPoly α) = ofValues α := by
  simp [linPoly, ofValues, map_sum, Algebra.smul_def]

theorem degree_permMono {n : ℕ} (w : Equiv.Perm (Fin n)) :
    Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n := by
  rw [map_sum]; simp [Finsupp.degree_single]

theorem topCoeff_eq_zero_of_isHomogeneous {n d : ℕ} {Q : MvPolynomial (Fin n × Fin n) ℂ} (hQ : Q.IsHomogeneous d)
    (hd : d ≠ n) : topCoeff Q = 0 := by
  unfold topCoeff
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [hQ.coeff_eq_zero (by rw [degree_permMono]; exact fun h => hd h.symm), mul_zero]

theorem dens_aeval_ofValues_offDeg : ∀ (n : ℕ) (κ : Type) (α : κ → V n → V n → ℂ) (d : ℕ) (P : MvPolynomial κ ℝ),
    P.IsHomogeneous d → d ≠ n →
      dens ((aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) : Alt n) = 0 := by
  intro n κ α d P hP hd
  have h1 : (aeval (fun i => ofValues (α i)) (P.map (algebraMap ℝ ℂ)) : Ev n) =
      aeval sym (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))) := by
    rw [aeval_bind₁]; simp only [aeval_sym_linPoly]
  have hQ : (bind₁ (fun i => linPoly (α i)) (P.map (algebraMap ℝ ℂ))).IsHomogeneous d := by
    simpa using (hP.map (algebraMap ℝ ℂ)).aeval (fun i => linPoly (α i)) fun i => linPoly_isHomogeneous (α i)
  rw [h1, GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar, topCoeff_eq_zero_of_isHomogeneous hQ hd, zero_div]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionSectionOfSpreadThroughLatticeMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem GlobalTheory.Poinc.Sep.Spz.torAt_of_spread₂ : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (o : Type) [CommRing o] (s : B ⟶ Sp o) (o₁ : o →+* V₁) (o₂ : o →+* V₂), ξ₁ ≫ s = spMap o₁ → ξ₂ ≫ s = spMap o₂ → ∀ (k : ℕ) (ζ : o), 1 ≤ k → IsUnit (k : o) → ζ ^ k = 1 → ∀ (Wo : B.Opens) (h : Wo.toScheme ⟶ H.left) (ξ₁' : Sp V₁ ⟶ Wo.toScheme) (ξ₂' : Sp V₂ ⟶ Wo.toScheme), h ≫ H.hom = Wo.ι → ξ₁' ≫ Wo.ι = ξ₁ → ξ₂' ≫ Wo.ι = ξ₂ → ∀ (F₁ : Type) [Field F₁] [IsAlgClosed F₁] [Algebra (FractionRing V₁) F₁] (F₂ : Type) [Field F₂] [IsAlgClosed F₂] [Algebra (FractionRing V₂) F₂] (c : D₁.toPre.X →+ ℤ) (x₁ : TFK (R := V₁) F₁ ⟶ A₁.A) (x₂ : TFK (R := V₂) F₂ ⟶ A₂.A), TorAt U₁ F₁ k (algebraMap (FractionRing V₁) F₁ (algebraMap V₁ (FractionRing V₁) (o₁ ζ))) c x₁ → x₁.left ≫ genMap U₁ ≫ β₁ = spMap (algebraMap (FractionRing V₁) F₁) ≫ jK V₁ ≫ ξ₁' ≫ h → x₂ ^ k = 1 → x₂.left ≫ genMap U₂ ≫ β₂ = spMap (algebraMap (FractionRing V₂) F₂) ≫ jK V₂ ≫ ξ₂' ≫ h → TorAt U₂ F₂ k (algebraMap (FractionRing V₂) F₂ (algebraMap V₂ (FractionRing V₂) (o₂ ζ))) (c.comp ρ) x₂ := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ ρ hS o _ s o₁ o₂ hs₁ hs₂ k ζ hk hku hζ Wo h ξ₁' ξ₂' hh h₁ h₂ F₁ _ _ _ F₂ _ _ _ c x₁ x₂ hx₁ hx₁g hx₂ hx₂g
  have hw₁ : o₁ ζ ^ k = 1 := by rw [← map_pow, hζ, map_one]
  have hw₂ : o₂ ζ ^ k = 1 := by rw [← map_pow, hζ, map_one]
  have hA := GlobalTheory.T.toricTorsionSection_eq_torusPoint_at_closedPointField B H V₁ hV₁ G₁ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ (ξ₁' ≫ h) (by rw [Category.assoc, hh, h₁]) k (o₁ ζ) hk hw₁
    F₁ c x₁ hx₁ hx₁g
  obtain ⟨κ, _, b, hb, Gκ, _, m, hm, τ, z, hτ, hz, he⟩ := GlobalTheory.T.torusPointSection_along_spreadingTrait B H hH V₁ G₁ D₁ A₁ U₁ ξ₁ β₁ V₂ G₂ D₂ A₂ U₂ ξ₂ β₂ ρ
    hS o s o₁ o₂ hs₁ hs₂ k ζ hk hζ Wo h ξ₁' ξ₂' hh h₁ h₂ c hA
  exact GlobalTheory.T.toricTorsionPoint_of_torusPoint_at_closedPointField B H V₂ hV₂ G₂ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ (ξ₂' ≫ h) (by rw [Category.assoc, hh, h₂]) k (o₂ ζ) hk
    (by simpa using hku.map o₂) hw₂ F₂ (c.comp ρ) x₂ hx₂ hx₂g κ b hb Gκ m hm τ hτ z hz he
end

