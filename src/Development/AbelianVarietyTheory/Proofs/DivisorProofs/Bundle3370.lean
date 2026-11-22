import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemSubringOfLocalInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3365
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankFormMinimalTuplesAtClosedPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureOfCoheightField
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VdmRec.CutSec

section General

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt GlobalTheory.Cartier

theorem exists_finite_specializes {T : Type*} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T] {C : Set T}
    (hC : IsClosed C) : ∃ G : Set T, G.Finite ∧ G ⊆ C ∧ ∀ x ∈ C, ∃ g ∈ G, g ⤳ x := by
  obtain ⟨S, hS, hcl, hirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  choose g hg using fun t : S => QuasiSober.sober (hirr t t.2) (hcl t t.2)
  have := hS.to_subtype
  refine ⟨Set.range g, Set.finite_range g, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨t, t.2, (hg t).mem⟩
  · rintro x ⟨t, ht, hx⟩
    exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, (hg ⟨t, ht⟩).specializes hx⟩

theorem dim_closure_of_coheight_field {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (t : X ⟶ Spec (.of K))
    [LocallyOfFiniteType t] {n : ℕ} (hX : topologicalKrullDim X = (n + 1 : ℕ)) {w : X} (hw : Order.coheight w = 1) :
    topologicalKrullDim (closure ({w} : Set X)) = n := by
  have hgen : genericPoint X ∉ closure ({w} : Set X) := by
    intro h
    have e : w = genericPoint X :=
      ((genericPoint_specializes w).antisymm (specializes_iff_mem_closure.2 h)).eq.symm
    rw [e, Order.coheight_eq_zero.2 (fun y _ => genericPoint_specializes y)] at hw
    exact zero_ne_one hw
  have hX1 : topologicalKrullDim (Set.univ : Set X) = (n + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hX
  have hup : topologicalKrullDim (closure ({w} : Set X)) + 1 ≤ (n + 1 : ℕ) :=
    hX1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ
      fun x _ => ⟨genericPoint X, trivial, hgen, genericPoint_specializes x⟩
  refine le_antisymm (GlobalTheory.PullVanish.withBot_le_of_add_one_le hup) ?_
  obtain ⟨A, _, _, _, _, _, j, _, ⟨a, ha⟩, -, hA⟩ := exists_affine_chart_trdeg_eq t w
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast K (A := A)
  have hdimX : topologicalKrullDim X ≤ (d : ℕ) := by
    refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨B, _, _, _, _, _, j', _, ⟨b, rfl⟩, -, hB⟩ := exists_affine_chart_trdeg_eq t x
    refine ⟨Set.range j', j'.isOpenEmbedding.isOpen_range, ⟨b, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding j'.isOpenEmbedding.isEmbedding rfl]
    exact ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).trans
      (ringKrullDim_eq_of_trdeg_eq K B (hB.trans (hA.symm.trans hd)))).le
  have hh : a.asIdeal.height = 1 := by
    rw [← hw, ← ha, coheight_apply_of_isOpenImmersion]
    exact idealHeight_eq_coheight (CommRingCat.of A) a
  have : a.asIdeal.IsPrime := a.isPrime
  have hF := height_add_ringKrullDim_quotient_of_finiteType K a.asIdeal
  rw [hh, ringKrullDim_eq_of_trdeg_eq K A hd] at hF
  have hlow : topologicalKrullDim (Set.range j ∩ closure {j a} : Set X) ≤
      topologicalKrullDim (closure ({w} : Set X)) := by
    rw [ha]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j a] at hlow
  refine le_trans ?_ hlow
  rw [hX, ← hF] at hdimX
  generalize ringKrullDim (A ⧸ a.asIdeal) = u at hdimX
  induction u using WithBot.recBotCoe with
  | bot => simp at hdimX
  | coe u =>
    induction u using ENat.recTopCoe with
    | top => exact_mod_cast le_top
    | coe u =>
      have : n + 1 ≤ 1 + u := by exact_mod_cast hdimX
      exact_mod_cast (by omega : n ≤ u)

theorem dim_closure_of_coheight {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] {n : ℕ} (hZ : topologicalKrullDim Z = (n + 1 : ℕ)) {w : Z}
    (hw : Order.coheight w = 1) : topologicalKrullDim (closure ({w} : Set Z)) = n := by
  obtain ⟨l, hl⟩ := CharP.exists Γ(Z, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Z, ⊤) l with hp | rfl
  · have : Fact l.Prime := ⟨hp⟩
    let := ZMod.algebra Γ(Z, ⊤) l
    obtain ⟨N, jN, _, hjN⟩ := hX.isProjOver
    have := isProper_str k N
    have : IsProper p := hjN ▸ inferInstance
    have : IsFinite (spMap (Int.castRingHom k)) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
    have e : strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : LocallyOfFiniteType (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))) := e ▸ inferInstance
    have : LocallyOfFiniteType (strHom (ZMod l) Z) := locallyOfFiniteType_of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact dim_closure_of_coheight_field (strHom (ZMod l) Z) hZ hw
  · have := CharP.charP_to_charZero Γ(Z, ⊤)
    have h := GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one k Z (i ≫ p) n (hX.of_isClosedImmersion i this hZ) _
      (redι (clo w)) (by rw [GlobalTheory.PullVanish.redι_genericPoint]; exact hw)
    exact (topologicalKrullDim_eq_of_isEmbedding (redι (clo w)).isClosedEmbedding.isEmbedding
      (range_redι _)).trans h

theorem charZero_of_specializes {X : Scheme.{0}} {z w : X} (h : z ⤳ w) (hw : CharZero (X.residueField w)) :
    CharZero (X.residueField z) := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  have h₁ : IsUnit (n : X.presheaf.stalk w) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
    exact (Nat.cast_ne_zero (R := X.residueField w)).2 h0
  have h₂ := (h₁.map (X.presheaf.stalkSpecializes h).hom).map (X.residue z).hom
  rw [map_natCast, map_natCast, hn] at h₂
  exact not_isUnit_zero h₂

theorem exists_of_cutMult_ne_zero {X : Scheme.{0}} [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB) (s : L.Sec) {z w : X}
    (h : cutMult hL s z w ≠ 0) :
    ∃ w', redι (clo z) w' = w ∧ Order.coheight w' = 1 ∧ w ∉ Out.nonzeroLocus s := by
  have : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal (clo z)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (redι (clo z))
  unfold cutMult at h
  split_ifs at h with hg
  · by_cases hw : ∃ w', redι (clo z) w' = w
    · obtain ⟨w', rfl⟩ := hw
      rw [(redι (clo z)).isClosedEmbedding.injective.extend_apply] at h
      refine ⟨w', rfl, CartierDiv.coheight_eq_one_of_mult_ne_zero h, fun hs => ?_⟩
      refine notMem_supp_divOfSec.2 ?_ (CartierDiv.mem_supp_of_mult_ne_zero h)
      rw [GlobalTheory.ZV.GraphSystem.nonzeroLocus_pull]
      exact hs
    · rw [Function.extend_apply' _ _ _ hw] at h
      exact absurd rfl h
  · exact absurd rfl h

end General

section Cut

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ArInt GlobalTheory.Cartier

theorem exists_sec_preimage {k : Type} [CommRing k] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {a n : ℕ} (ha : 0 < a)
    (f : X ⟶ PSpace k n) (iso : LBIso ((ProjSpace.O1 k n).pull f) (lbPow L a)) {S : Set (PSpace k n)} (hS : S.Finite) :
    ∃ m, 0 < m ∧ ∃ (s : (lbPow L m).Sec) (U : (PSpace k n).Opens), S ⊆ U ∧ Out.nonzeroLocus s = f ⁻¹ᵁ U := by
  obtain ⟨r, hr, t, ht, -, -⟩ := (isAmple_projective_O_one k n).exists_affine_finite_subset hS (U := ⊤) (Set.subset_univ _)
  have h1 := ProjSpace.O1_isLB k n
  obtain ⟨t₁, e₁⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow (LB.isLB_pull h1 f) r)
    (LB.isLB_pull (isLB_lbPow h1 r) f) (lbIso_lbPow_pull h1 f r) (GlobalTheory.secPull t f)
  obtain ⟨t₂, e₂⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow (isLB_lbPow hL a) r)
    (isLB_lbPow (LB.isLB_pull h1 f) r) (lbIso_lbPow iso r).symm t₁
  obtain ⟨t₃, e₃⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow hL (a * r))
    (isLB_lbPow (isLB_lbPow hL a) r) (lbIso_lbPow_lbPow hL a r).symm t₂
  exact ⟨a * r, Nat.mul_pos ha hr, t₃, _, ht, by rw [e₃, e₂, e₁, GlobalTheory.nonzeroLocus_secPull]⟩

theorem exists_cut {k : Type} [CommRing k] {X : Scheme.{0}} [IsLocallyNoetherian X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {L : LB X} (hL : L.IsLB) (hL' : ∀ m, (lbPow L m).IsLB) {a n : ℕ} (ha : 0 < a)
    (f : X ⟶ PSpace k n) (hf : f ≫ PSpace.str k n = p) (iso : LBIso ((ProjSpace.O1 k n).pull f) (lbPow L a))
    {B : Set X} (hB : IsClosed B) {z : X} {e : ℕ}
    (h₁ : topologicalKrullDim (closure ({z} : Set X)) = (e + 1 + 2 : ℕ))
    (h₂ : topologicalKrullDim (f '' (closure {z} ∩ B)) + 3 ≤ (e + 1 + 2 : ℕ))
    (h₃ : CharZero (X.residueField z) → z ∉ B) :
    ∃ m, 0 < m ∧ ∃ s : (lbPow L m).Sec, z ∈ Out.nonzeroLocus s ∧ ∀ w, cutMult (hL' m) s z w ≠ 0 →
      topologicalKrullDim (closure ({w} : Set X)) = (e + 2 : ℕ) ∧
      topologicalKrullDim (f '' (closure {w} ∩ B)) + 3 ≤ (e + 2 : ℕ) ∧ (CharZero (X.residueField w) → w ∉ B) := by
  have := hX.isNoetherian
  have : IsProper f := by
    obtain ⟨N, jN, _, hjN⟩ := hX.isProjOver
    have := isProper_str k N
    have := isProper_str k n
    have : IsProper p := hjN ▸ inferInstance
    have : IsProper (f ≫ PSpace.str k n) := hf ▸ this
    exact IsProper.of_comp f (PSpace.str k n)
  have hC : IsClosed (closure {z} ∩ B) := isClosed_closure.inter hB
  obtain ⟨G, hG, hGC, hGs⟩ := exists_finite_specializes hC
  obtain ⟨m, hm, s, U, hU, hs⟩ := exists_sec_preimage hL ha f iso ((hG.insert z).image f)
  have hGU : ∀ g ∈ G, f g ∈ U := fun g hg => hU ⟨g, Or.inr hg, rfl⟩
  refine ⟨m, hm, s, hs ▸ hU ⟨z, Or.inl rfl, rfl⟩, fun w hw => ?_⟩
  obtain ⟨w', hw', hco, hwU⟩ := exists_of_cutMult_ne_zero _ s hw
  rw [hs] at hwU
  replace hwU : f w ∉ U := hwU
  have emb := (redι (clo z)).isClosedEmbedding
  have hzw : z ⤳ w := specializes_iff_mem_closure.2 (by
    have : w ∈ Set.range (redι (clo z)) := ⟨w', hw'⟩
    rwa [range_redι] at this)
  refine ⟨?_, ?_, fun hw0 hwB => ?_⟩
  · have hZ := (topologicalKrullDim_eq_of_isEmbedding emb.isEmbedding (range_redι _)).symm.trans h₁
    have h := dim_closure_of_coheight hX (redι (clo z)) (n := e + 2) hZ hco
    rw [← h]
    refine topologicalKrullDim_eq_of_isEmbedding (emb.isEmbedding.comp IsEmbedding.subtypeVal) ?_
    rw [Set.range_comp, Subtype.range_coe, ← emb.closure_image_eq, Set.image_singleton, hw']
  · have hfC : IsClosed (f '' (closure {z} ∩ B)) := f.isClosedMap _ hC
    have h₄ := topologicalKrullDim_add_one_le (hfC.sdiff U.isOpen) hfC (by
      rintro _ ⟨⟨x, hx, rfl⟩, -⟩
      obtain ⟨g, hg, hgx⟩ := hGs x hx
      exact ⟨f g, ⟨g, hGC hg, rfl⟩, fun h => h.2 (hGU g hg), hgx.map f.continuous⟩)
    have h₅ : f '' (closure {w} ∩ B) ⊆ f '' (closure {z} ∩ B) \ U := by
      rintro _ ⟨x, ⟨hx, hxB⟩, rfl⟩
      have hwx : w ⤳ x := specializes_iff_mem_closure.2 hx
      exact ⟨⟨x, ⟨specializes_iff_mem_closure.1 (hzw.trans hwx), hxB⟩, rfl⟩,
        fun h => hwU ((hwx.map f.continuous).mem_open U.isOpen h)⟩
    have h₆ := (IsEmbedding.inclusion h₅).isInducing.topologicalKrullDim_le
    refine GlobalTheory.PullVanish.withBot_le_of_add_one_le ?_
    calc topologicalKrullDim (f '' (closure {w} ∩ B)) + 3 + 1
        = topologicalKrullDim (f '' (closure {w} ∩ B)) + 1 + 3 := add_right_comm _ _ _
      _ ≤ topologicalKrullDim (f '' (closure {z} ∩ B)) + 3 := by
        gcongr
        exact le_trans (by gcongr) h₄
      _ ≤ _ := h₂
  · have hzB := h₃ (charZero_of_specializes hzw hw0)
    obtain ⟨g, hg, hgw⟩ := hGs w ⟨specializes_iff_mem_closure.1 hzw, hwB⟩
    obtain ⟨g', rfl⟩ : g ∈ Set.range (redι (clo z)) := by
      rw [range_redι]
      exact (hGC hg).1
    subst hw'
    have l₁ : w' < g' := ⟨emb.isInducing.specializes_iff.1 hgw, fun h =>
      hwU (((show w' ⤳ g' from h).map (redι (clo z) ≫ f).continuous).mem_open U.isOpen (hGU _ hg))⟩
    have l₂ : g' < genericPoint _ := ⟨genericPoint_specializes g', fun h => hzB (by
      have := ((show g' ⤳ genericPoint _ from h).map emb.continuous).mem_closed hB (hGC hg).2
      rwa [GlobalTheory.PullVanish.redι_genericPoint] at this)⟩
    have h₄ := Order.coheight_add_one_le l₁
    have h₅ := Order.coheight_add_one_le l₂
    rw [hco] at h₄
    have h₆ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₅) 1).trans h₄
    exact absurd h₆ (by decide)

end Cut

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec

theorem isClosed_bd {D : D7} {O : Setup D} {c : O.s.Comp} (M : DRBase O c) : IsClosed M.bd := by
  have := M.ar.isNoetherianRing
  have := isNoetherian_of_isProjOver O.s.T.Z.proj
  exact ((GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian O.s.T.Z.t.G O.s.T.Z.t.semi).preimage
    M.b.continuous).isClosed_compl

theorem exists_cuts : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (I : M.Emb) (z : M.B) (e : ℕ), I.Good z (e + 1) → ∃ m : ℕ, 0 < m ∧ ∃ s : (lbPow M.lamB m).Sec, I.Cuts s z e := by
  intro D O c M I z e h
  exact exists_cut M.ar (M.lam 2).isLB M.isLB_pow I.a_pos I.f I.f_str I.iso (isClosed_bd M) h.1 h.2.1 h.2.2

end GlobalTheory.VdmRec.CutSec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapComp
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogKSUp

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem chart_res' {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE h).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
  U.2.map_fromSpec W.2 (homOfLE h).op

theorem exists_factor {X : Scheme.{0}} (U W : X.affineOpens) (h : W.1 ≤ U.1) {S : Type} [CommRing S]
    (φ : Γ(X, U.1) →+* S) (hr : ∀ z, (spMap φ ≫ GlobalTheory.LogKS.chart U) z ∈ W.1) :
    ∃ φ' : Γ(X, W.1) →+* S, φ = φ'.comp (X.presheaf.map (homOfLE h).op).hom := by
  have hr' : Set.range (spMap φ ≫ GlobalTheory.LogKS.chart U) ⊆ Set.range (GlobalTheory.LogKS.chart W) := by
    show _ ⊆ Set.range (IsAffineOpen.fromSpec W.2)
    rw [W.2.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact hr z
  have : IsOpenImmersion (GlobalTheory.LogKS.chart W) := W.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (GlobalTheory.LogKS.chart U) := U.2.isOpenImmersion_fromSpec
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Sp S ⟶ Sp Γ(X, W.1), ψ ≫ GlobalTheory.LogKS.chart W = spMap φ ≫ GlobalTheory.LogKS.chart U :=
    ⟨IsOpenImmersion.lift (GlobalTheory.LogKS.chart W) _ hr', IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨(Spec.preimage ψ).hom, ?_⟩
  have hfac : spMap (Spec.preimage ψ).hom ≫ GlobalTheory.LogKS.chart W = spMap φ ≫ GlobalTheory.LogKS.chart U := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
    exact hψ
  rw [← chart_res' U W h, ← Category.assoc, spMap_comp''] at hfac
  have h2 := Spec.map_inj.1 ((cancel_mono (GlobalTheory.LogKS.chart U)).1 hfac)
  simpa using (congrArg CommRingCat.Hom.hom h2).symm

end GlobalTheory.LogKSUp

namespace GlobalTheory.LogKSUp

theorem isKS_of_inf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U W : X.affineOpens) (hW : W.1 = U.1 ⊓ V) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1)) (DW : Γ(X, W.1) → Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ r, DW ((X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D r)) → IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW ((X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom.mapMatrix Θ) → IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U W hW n v D DW Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩
  have hWU : W.1 ≤ U.1 := hW.le.trans inf_le_left
  have hWW : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ W.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, Wc, j, d, ?_, hj, hfld, fun i h r => ?_, fun i i' O hO f S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [hsup, hW, inf_assoc, inf_idem]
  · have e : ∀ r : Γ(X, U.1), (t.G.hom.appLE U.1 (Wc i) h).hom r =
        (t.G.hom.appLE W.1 (Wc i) (hWW i)).hom ((X.presheaf.map (homOfLE hWU).op).hom r) := by
      intro r
      exact (congrArg (fun k => k.hom r) (t.G.hom.map_appLE (hWW i) (homOfLE hWU).op)).symm
    rw [e, e, hcomp i (hWW i), hD]
  · have hr : ∀ z, (spMap φ ≫ GlobalTheory.LogKS.chart U) z ∈ W.1 := by
      intro z
      rw [← hg₀]
      have hz : g₀ z ∈ O := hO' (show z ∈ (⊤ : (Sp S).Opens) from trivial)
      exact hWW i (inf_le_left (a := Wc i) (b := Wc i') (hO hz))
    obtain ⟨φ', hfac⟩ := exists_factor U W hWU φ hr
    have hg₀' : g₀ ≫ t.G.hom = spMap φ' ≫ GlobalTheory.LogKS.chart W := by
      rw [hg₀, hfac, ← spMap_comp'', Category.assoc, chart_res']
    have := htest i i' O hO f S φ' g₀ w hg₀' hO' fun a => by
      obtain ⟨g', v', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v', h₁, ?_, h₃⟩
      rw [h₂, ← Category.assoc, spMap_comp'', dualMap_comp'', ← hfac]
    rw [this]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hfac]
    rfl

end GlobalTheory.LogKSUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigRank
section
noncomputable section

open AlgebraicGeometry NumberField
open scoped Matrix

namespace GlobalTheory.BalProj

def eigSp {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k) :
    Submodule k (Fin n → k) where
  carrier := {c | ∀ a, c ᵥ* B a = χ a • c}
  zero_mem' := fun a => by simp
  add_mem' := fun {c d} hc hd a => by rw [Matrix.add_vecMul, hc a, hd a, smul_add]
  smul_mem' := fun r c hc a => by rw [Matrix.smul_vecMul, hc a, smul_comm]

def eigRank {O R k : Type} [CommRing R] [Field k] (φ : R →+* k) {n : ℕ} (A : O → Matrix (Fin n) (Fin n) R)
    (χ : O → R) : ℕ :=
  Module.finrank k (eigSp (fun a => (A a).map φ) (fun a => φ (χ a)))

def embR {E : Type} [Field E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) {R : Type}
    [CommRing R] (ι : F →+* R) (τ : E →+* ℂ) (a : 𝓞 E) : R :=
  ι ⟨τ (a : E), hF τ a⟩

def fnHom {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (s.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

end GlobalTheory.BalProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsIntClosedLocalDomain
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.HtpyLine

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]
  rw [← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]

theorem pull_bijective_of_ringEquiv {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (F : Shv R) (n : ℤ) : Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : spMap (e.symm : B →+* A) ≫ spMap (e : A →+* B) = 𝟙 _ := by
    rw [← spMap_comp, ← spMap_id]
    congr 1
    ext x
    simp
  have h2 : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 _ := by
    rw [← spMap_comp, ← spMap_id]
    congr 1
    ext x
    simp
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (spMap (e.symm : B →+* A)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h1, pull_id]
  · rw [← pull_comp, h2, pull_id]

theorem bijective_of_subsingleton {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Subsingleton M] [Subsingleton N]
    (f : M →+ N) : Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end GlobalTheory.EtC.HtpyLine

namespace GlobalTheory.EtC.HtpyLine

open Polynomial

theorem exists_cyclotomic_root_of_AIC (q : ℕ) [NeZero q] (T : Type) [CommRing T] [Nontrivial T] (hA : AIC T) :
    ∃ ζ : T, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨a, ha⟩ := hA (cyclotomic q T) (cyclotomic.monic q T)
    (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
  refine ⟨a, ?_⟩
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
  exact ha

theorem htpy_AIC : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : T →+* Polynomial T)) (tw q i) := by
  intro q _ T _ _ _ hA hq i n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1 (sp T) n hn
    haveI := (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1 (sp (Polynomial T)) n hn
    exact bijective_of_subsingleton _
  · exact GlobalTheory.T.h_zero_pullback_twist_bijective q T (Polynomial T) Polynomial.C hq (exists_cyclotomic_root_of_AIC q T hA) inferInstance
      (fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he) (fun e he => IsIdempotentElem.iff_eq_zero_or_one.mp he) i
  · haveI hT : Subsingleton (Ht q (sp T) n i) := GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic q T hA hq n i hn
    haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
    have hqK : IsUnit (q : FractionRing T) := by simpa using hq.map (algebraMap T (FractionRing T))
    haveI hKt : Subsingleton (Ht q (sp (Polynomial (FractionRing T))) n i) := GlobalTheory.T.tateTwistAcyclic_spectrum_polynomial_of_isAlgClosed q (FractionRing T) hqK n i hn
    let e : TensorProduct T (FractionRing T) (Polynomial T) ≃+* Polynomial (FractionRing T) :=
      (polyEquivTensor T (FractionRing T)).symm.toRingEquiv
    haveI hTens : Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) (Polynomial T))) n i) :=
      (pull_bijective_of_ringEquiv e (tw q i) n).1.subsingleton
    have hC3 := GlobalTheory.T.etale_cohomology_ind_etale_base_change q T hA hq (Polynomial T) i n
    haveI : Subsingleton (Ht q (sp (Polynomial T)) n i) := hC3.1.subsingleton
    exact bijective_of_subsingleton _

end GlobalTheory.EtC.HtpyLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleDieudonneBaseByCartierDualityStatement
section
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality : ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn)), ∃ Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt), Be.EtDual Bc := by
  first | exact @GlobalTheory.dieuBase_isEt_of_isConn | exact GlobalTheory.dieuBase_isEt_of_isConn | (intros; apply GlobalTheory.dieuBase_isEt_of_isConn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnramifiedRepresentingPolarizedHomsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_unramified_representing_polarizedHoms : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, IsFinite R.π ∧ FormallyUnramified R.π := by
  first | (exact @GlobalTheory.EndLoc.HomFixFinite.exists_finite_unramified) | (exact GlobalTheory.EndLoc.HomFixFinite.exists_finite_unramified) | (intros; apply GlobalTheory.EndLoc.HomFixFinite.exists_finite_unramified  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantSmoothProjFanNoSelfIntersectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_smoothProjFan_noSelfIntersections : ∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ := by
  first | exact @GlobalTheory.PolDeg.exists_inv_smooth_fan_noSelfInt | exact GlobalTheory.PolDeg.exists_inv_smooth_fan_noSelfInt | (intros; apply GlobalTheory.PolDeg.exists_inv_smooth_fan_noSelfInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankFormMinimalTuplesAtClosedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_form_minimalTuples_at_closedPoint : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∀ (_ : NeZero S.N) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (r : ℕ) (b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : (Fin 8 → Fin r → ZMod S.N) → (Fin 8 → Fin r → ℤ)) (e : (Fin 8 → Fin r → ZMod S.N) → Ω), r ≤ g ∧ (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧ (∀ c u i, ((μ c u i : ℤ) : ZMod S.N) = c u i) ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) ∧ (∀ c, e c ≠ 0 ∧ ∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e c = S.FF T₀ c' κ / S.th x₀) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : (Fin r → ℤ) →+ T.D.toPre.X, Function.Surjective π ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) α) ∧ ∀ c, 0 ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ∧ OrdEq M T ξ (e c ^ S.N) (qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c)).toNat := by
  first | exact @GlobalTheory.Poinc.Clocx.exists_at_closedPoint | exact GlobalTheory.Poinc.Clocx.exists_at_closedPoint | (intros; apply GlobalTheory.Poinc.Clocx.exists_at_closedPoint <;> assumption)
end

