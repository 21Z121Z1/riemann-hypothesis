import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0027
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0042
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0083
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0089
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SpanMulMem

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CardRootsBar
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

noncomputable section

namespace UpperTheory.GalS

theorem om_gen_inj {D : D7} (P : PairedCharacterCondition.Pend D) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k))
    {γ : GE D.nd} (hγ : TameGenAt (D.nd.plOm.1 w) γ) {x y : Fb (D.host.g k) (D.host.g_prime k)} (hx : x ≠ 0) (hy : y ≠ 0)
    (e : P.om k w x γ = P.om k w y γ) : x = y := by
  by_contra hne
  obtain ⟨σ, hσ, hd⟩ := P.om_inj k w hw x y hx hy hne
  obtain ⟨U, hU, hUx⟩ := P.om_open k w x hx
  obtain ⟨V, hV, hVy⟩ := P.om_open k w y hy
  have inv : ∀ z, z ≠ 0 → ∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), P.om k w z a * P.om k w z a⁻¹ = 1 := fun z hz a ha => by
    rw [← P.om_mul k w z hz a ha _ (inv_mem ha), mul_inv_cancel, P.om_one k w z hz]
  let K : Subgroup (GE D.nd) :=
    { carrier := {s | s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) ∧ P.om k w x s = P.om k w y s}
      one_mem' := ⟨one_mem _, by rw [P.om_one k w x hx, P.om_one k w y hy]⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [P.om_mul k w x hx a ha.1 b hb.1, P.om_mul k w y hy a ha.1 b hb.1, ha.2, hb.2]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have h1 := inv x hx a ha.1
        have h2 := inv y hy a ha.1
        rw [ha.2] at h1
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h2) (h1.trans h2.symm)⟩ }
  have hK : Subgroup.closure (insert γ (wildSet D.nd (D.nd.plOm.1 w))) ≤ K := by
    rw [Subgroup.closure_le]
    rintro s (rfl | hs)
    · exact ⟨hγ.1, e⟩
    · exact ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hs, by rw [P.om_wild k w hw x hx s hs, P.om_wild k w hw y hy s hs]⟩
  have hO : IsOpen {s : GE D.nd | σ⁻¹ * s ∈ (U : Set (GE D.nd)) ∩ V} := (hU.inter hV).preimage (continuous_mul_left σ⁻¹)
  obtain ⟨s, hs1, hs2⟩ := mem_closure_iff.1 (hγ.2 hσ) _ hO (by simp [U.one_mem, V.one_mem])
  have hs := hK hs2
  have hi : σ⁻¹ * s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := mul_mem (inv_mem hσ) hs.1
  have e1 := P.om_mul k w x hx σ hσ _ hi
  have e2 := P.om_mul k w y hy σ hσ _ hi
  rw [mul_inv_cancel_left, hUx _ hs1.1 hi, mul_one] at e1
  rw [mul_inv_cancel_left, hVy _ hs1.2 hi, mul_one] at e2
  exact hd (e1.symm.trans (hs.2.trans e2))

theorem om_pow {D : D7} (P : PairedCharacterCondition.Pend D) (k : Fin 2) (w : PlE D.host) {γ : GE D.nd}
    (hγ : γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) {x : Fb (D.host.g k) (D.host.g_prime k)} (hx : x ≠ 0) (n : ℕ) (h : x ^ n = 1) :
    P.om k w x γ ^ n = 1 := by
  have h1 : P.om k w 1 γ = 1 := by
    have a := P.tameInertiaChar_mul_root k w 1 1 one_ne_zero one_ne_zero γ hγ
    have b := P.om_mul k w 1 one_ne_zero γ hγ _ (inv_mem hγ)
    rw [mul_inv_cancel, P.om_one k w 1 one_ne_zero] at b
    rw [mul_one] at a
    exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one b.symm) (a.symm.trans (mul_one _).symm)
  have h2 : ∀ m : ℕ, P.om k w (x ^ m) γ = P.om k w x γ ^ m := fun m => by
    induction m with
    | zero => rw [pow_zero, pow_zero, h1]
    | succ m ih => rw [pow_succ, pow_succ, P.tameInertiaChar_mul_root k w _ _ (pow_ne_zero _ hx) hx γ hγ, ih]
  rw [← h2, h, h1]

theorem card_rootsBar {p : ℕ} [Fact p.Prime] (a : (ZMod p)[X]) : Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_map]

theorem nc_of_roots {D : D7} (P : PairedCharacterCondition.Pend D) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k))
    (y : D.naut.LP w) (hm : D.naut.mono0 y) (hdeg : (D.naut.items₂ k w y).natDegree = D.naut.lpDim y)
    (hle : D.naut.lpDim y ≤ D.R.nV)
    (hnz : haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∀ x ∈ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w y), x ≠ 0)
    (hrep : haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∀ x, x ::ₘ {x} ≤ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w y) → x ^ (D.host.g k - 1) = 1) :
    Nc D.nd D.naut y := by
  classical
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  refine ⟨fun σ hσ hwild => ?_, hm, fun γ hγ z hz => ?_⟩
  · rw [P.inertiaCharpoly_eigenvalues k w hw _ hdeg σ hσ,
      Multiset.map_congr rfl (fun x hx => by rw [P.om_wild k w hw x (hnz x hx) σ hwild, C_1]),
      Multiset.map_const', Multiset.prod_replicate, card_rootsBar, hdeg]
  · rw [P.inertiaCharpoly_eigenvalues k w hw _ hdeg γ hγ.1, thr_split (D.host.g_prime k) hw (D.nd.g_split k) (DiscreteGroups.sglob.DzType.big_of_le_nV D k hle)] at hz
    set M := Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w y) with hM
    have e : (M.map fun x => X - C (P.om k w x γ)).prod = ((M.map fun x => P.om k w x γ).map fun c => X - C c).prod := by
      rw [Multiset.map_map]; rfl
    rw [e, ← count_roots, roots_multiset_prod_X_sub_C] at hz
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.count_pos.1 (by omega : 0 < Multiset.count z (M.map fun x => P.om k w x γ)))
    rw [Multiset.count_map_eq_count _ _ (fun a ha b hb h => om_gen_inj P k w hw hγ (hnz a ha) (hnz b hb) h) x hx] at hz
    rw [GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw]
    exact om_pow P k w hγ.1 (hnz x hx) _ (hrep x (Multiset.le_count_iff_replicate_le.1 hz))

theorem nc_of_label {D : D7} (P : PairedCharacterCondition.Pend D) (hDZ : PairedCharacterCondition.admDZ P) (h1 : SumRepresentations.adm1 D) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k)
    (PI : D.naut.AV i) (τ : (P.lz k).Irr D.R.r) (hτ : τ ∈ P.kty i PI k v) (hsq : Squarefree ((P.lz k).lab τ))
    (hroot : ∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ →
      ¬ ((P.lz k).lab τ).IsRoot (u : ZMod (D.host.g k)))
    (w : PlE D.host) (hw : w = D.naut.plGw k v ∨ IsConjPl D.host (D.naut.plGw k v) w) :
    Nc D.nd D.naut (D.naut.locV i PI w) := by
  classical
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨u, hu, hm0, hlab, hconj⟩ := hDZ i k v PI τ hτ hsq hroot
  obtain ⟨Pa, -, -, hr, hs, -⟩ := h1 i PI
  have hdim : ∀ w, IsSplitPl D.host w → D.naut.lpDim (D.naut.locV i PI w) = D.R.nV := fun w h => by
    rw [← hs w h, GlobalTheory.InertialTypesCmp.lpDim_isoLoc, hr]
  have hne : (P.lz k).lab τ ≠ 0 := ((P.lz k).lab_spec τ).1.ne_zero
  have hroot0 : ∀ y ∈ Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t), y ≠ 0 := by
    rintro y hy rfl
    unfold Formalism.CyclotomicNorms.rootsBar at hy
    have h := isRoot_of_mem_roots hy
    rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, map_eq_zero, mul_coeff_zero, coeff_zero_eq_eval_zero (_ ^ _)] at h
    rcases mul_eq_zero.1 h with h | h
    · exact ((P.lz k).lab_spec τ).2.2 h
    · simp at h
  have hrep : ∀ x, 2 ≤ (Formalism.CyclotomicNorms.rootsBar ((P.lz k).lab τ * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).count x →
      x ^ (D.host.g k - 1) = 1 := by
    intro x hx
    unfold Formalism.CyclotomicNorms.rootsBar at hx
    have hnd := nodup_roots ((PerfectField.separable_iff_squarefree.2 hsq).map
      (f := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))))
    rw [Polynomial.map_mul, roots_mul (by
        rw [← Polynomial.map_mul]
        exact Polynomial.map_ne_zero (mul_ne_zero hne ((monic_X_sub_C _).pow _).ne_zero)),
      Multiset.count_add, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, roots_pow, roots_X_sub_C] at hx
    have h1 := Multiset.nodup_iff_count_le_one.1 hnd x
    have h2 : x ∈ D.R.t • ({algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k))} : Multiset _) :=
      Multiset.count_pos.1 (by omega)
    rw [Multiset.mem_singleton.1 (Multiset.mem_of_mem_nsmul h2), ← map_pow, ZMod.pow_card_sub_one_eq_one u.ne_zero, map_one]
  rcases hw with rfl | hc
  · refine nc_of_roots P k _ (D.naut.plGw_over k v) _ hm0 ?_ (hdim _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v)).le (by rw [hlab]; exact hroot0)
      (fun x hx => hrep x (Multiset.le_count_iff_replicate_le.2 (by rw [hlab] at hx; exact hx)))
    rw [hdim _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v), hlab, ((P.lz k).lab_spec τ).1.natDegree_mul ((monic_X_sub_C _).pow _),
      ((P.lz k).lab_spec τ).2.1, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    rfl
  · obtain ⟨hw, hs'⟩ := GlobalTheory.TypeAbove.conj_over_split D (D.naut.plGw_over k v) (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v) hc
    obtain ⟨hm, hdeg, hroots⟩ := hconj w hc
    refine nc_of_roots P k w hw _ hm (hdeg.trans (hdim w hs').symm) (hdim w hs').le ?_ fun x hx => ?_
    · rw [hroots]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
      exact inv_ne_zero (hroot0 z hz)
    · rw [hroots] at hx
      have h2 := Multiset.le_count_iff_replicate_le.2 (show Multiset.replicate 2 x ≤ _ from hx)
      rw [← inv_inv x, Multiset.count_map_eq_count' _ _ inv_injective] at h2
      have h3 := hrep _ h2
      rwa [inv_pow, inv_eq_one] at h3

end UpperTheory.GalS
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.HubXTypePrimeConditions
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace UpperTheory.GalS

theorem sq_old (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hG5 : SumRepresentations.ConclusionG5 D)
    (hHG : HG D.nd D.naut i) (hr : GoodR D.nd i r) (hLgc : GlobalTheory.HubX.LgcG D) (hDZ : GlobalTheory.HubX.DepthZeroG D) : PairedCharacterCondition.SetSQ i r :=
  GlobalTheory.T.local_global_compatibility_at_types D i r hG5 hHG hr (GlobalTheory.T.tame_descent_conditions_every_localisation D i).2 (GlobalTheory.T.tame_descent_conditions_every_localisation D i).1 fun w hw hwg => ⟨hLgc i r hr w hw hwg, hDZ i w hw hwg⟩
theorem noLgc : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → NoCondition D := fun _ _ _ _ _ => trivial

theorem hubX_typePrime_conditions : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → ParameterChoice' D L → AdmissibleParameterJ.JumpConditions L → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → SumRepresentations.ConclusionG5 D → GlobalTheory.HubX.LgcG D → GlobalTheory.HubX.DepthZeroG D → ∀ CT : ℕ, (CT : ℝ) ≤ L.sc.b → (∀ (i : D.nd.Loc) (k : Fin 2), TwistedPlaces.TwLoc D i → D.nd.l i = D.host.g k → HG D.nd D.naut i → GoodR D.nd i (X.r i) ∧ (∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (X.ρ i π) ∧ IsSSRep (rhoChiK D i (X.ρ i π))) ∧ ∃ (s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), X.eta + D.R.t + 1 < s ∧ CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k ∧ PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i (X.r i) X.eta s S sg U ∧ PairedCharacterCondition.SetSQ i (X.r i)) ∧ (X.eta : ℝ) ≤ 2 * L.etaSz := by
  intro D L HW R X hX P hJ hadm hG5 hLgc hDZ CT hCT
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hadm' : L.Sc + L.etaSz + D.R.t + 2 ≤ L.sc.b := hadm
  have hb : 1 ≤ L.sc.b := by linarith
  have ht : (D.R.t : ℝ) ≤ L.sc.b := by linarith
  obtain ⟨hnum1, hnum2, hnum3⟩ := GlobalTheory.typePrime_exceeds_constant D L P (by linarith) hb CT hCT
  obtain ⟨hJa, hJb, hJc, -, hJe, -, -⟩ := hJ
  have hJaAt : AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D (GlobalTheory.HubX.epJ D) := by
    rw [GlobalTheory.HubX.epJ_eq hJa]; exact hJa.choose_spec
  have hgood : ∀ i, GoodR D.nd i (X.r i) := hX.fam.good
  have hpt := GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D X.r X.ρ hX.fam
  rw [hX.eta]
  refine ⟨fun i k _ hk hHG => ⟨hgood i, fun π hπ => ⟨(hpt i π hπ).1, (hpt i π hπ).2.1⟩, ?_⟩, hnum2⟩
  obtain ⟨sg, U, hsg, hU⟩ := GlobalTheory.T.signs_and_jump_sets_at_type_prime D L (GlobalTheory.HubX.epJ D) hJaAt hJb hJc hJe ht i k (X.r i) hk (hgood i)
  have hSQ := sq_old D i (X.r i) hG5 hHG (hgood i) hLgc hDZ
  refine ⟨⌊3 * L.sc.b⌋₊ + 2, 0, sg, U, hnum1, hnum3 k, hsg, hU, hSQ⟩

end UpperTheory.GalS
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameGeneratorResidual
section
noncomputable section

namespace GlobalTheory.ResidualTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem cpAt' : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → GlobalTheory.RowTie.IotaRed D → UpperTheory.GalS.LabTameS D.nd D.naut → UpperTheory.GalS.RowRepAtGN D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩; Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) : Matrix (Fin D.R.r) (Fin D.R.r) _) = ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x => X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod := by
  intro D hT hI hL hR σ k v i hl hocc hgood
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨Sig, ρ, hP, hρ, hW⟩ := hR i σ hocc hgood
  obtain ⟨B, κ, h1, h2⟩ := hI i
  have hw := GlobalTheory.TameLabels.not_mem_of_ne (D := D) (k := k) (v := v) (D.nd.lPrime i).out hl
  obtain ⟨hιc, -⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  have hcont : Continuous (fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL (Fin D.R.r) (Qbar (D.nd.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i)))) := hρ.1.matrix_map hιc
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have hdim : D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) = D.R.r := by
    have h := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v)
    rwa [(hW k v hl).dim, D.naut.lpDim_tw] at h
  have hfull : (D.naut.items₂ k _ (D.naut.locW i σ (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) := by
    rw [← D.naut.lab_loc i k σ v, (D.nd.lab_monic k σ v).2, hdim]
  have hn : UpperTheory.GalS.Nc D.nd D.naut (D.naut.lpTw (D.naut.locW i σ (D.naut.plGw k v)) ((1 - (D.R.r : ℝ)) / 2)) :=
    (UpperTheory.GalS.nc_tw _ _).2 (hL.2 k v _ hfull (by rw [← D.naut.lab_loc i k σ v]; exact (hgood k).1.2.1 v)
      (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by rw [hdim]; unfold Ranks.nV; omega)))
  have hine : ((ρ (D.ntypes.tg k v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        (iotaO D.nd D.naut i) =
      ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x => X - C (D.ntypes.teichC k x)).prod := by
    have e := D.naut.wdOf_ine i (mapRep (iotaOQ D.nd D.naut i) ρ) _ hw hcont _ (D.ntypes.tg_mem k v)
    rw [(hW k v hl).ine hn _ (D.ntypes.tg_mem k v), D.naut.inePol_tw _ _ _ (D.ntypes.tg_mem k v), D.ntypes.inertiaCharpoly_type k v _ hfull,
      ← D.naut.lab_loc i k σ v] at e
    rw [hcomp, ← Polynomial.map_map, ← Matrix.charpoly_map]
    exact e
  have hred := GlobalTheory.TypeLeaf.map_eq_prod_of_valuationSubring B (iotaO D.nd D.naut i)
    (((fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom.comp
      κ.toRingHom).comp (IsLocalRing.residue B))
    ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) h1 (D.ntypes.teichC k)
    (fun x => fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
      (D.ntypes.iota k v (D.nd.w i) x))
    (fun x => by
      obtain ⟨h, e⟩ := h2 k v x
      exact ⟨h, congrArg (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out) e⟩)
    _ _ hine
  rw [← hT.2 i σ hocc hgood Sig ρ hP hρ (D.ntypes.tg k v)] at hred
  apply Polynomial.map_injective
    (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom
    (RingHom.injective _)
  rw [hred, Polynomial.map_multiset_prod, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
  simp [GlobalTheory.TypeLeaf.map_primeToPart_fbar]

end GlobalTheory.ResidualTame

namespace GlobalTheory.RowWildTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem main_alt : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → UpperTheory.GalS.LabTameS D.nd D.naut → UpperTheory.GalS.RowRepAtGN D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)), s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.ntypes.rbar σ (D.nd.w i) s = 1 := by
  intro D hT hL hR σ k v i hl hocc hgood s hs hwild
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨Sig, ρ, hP, hρ, hc⟩ := hR i σ hocc hgood
  have hw := GlobalTheory.TameLabels.not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  obtain ⟨hιc, hιi⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  have hcont : Continuous (fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL (Fin D.R.r) (Qbar (D.nd.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i)))) := hρ.1.matrix_map hιc
  have e := hc k v hl
  have hdim : D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) = D.R.r := by
    have := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v)
    rw [e.dim, D.naut.lpDim_tw] at this
    exact this
  have hfull : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locW i σ (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) := by
    rw [← D.naut.lab_loc i k σ v, (D.nd.lab_monic k σ v).2, hdim]
  have hn : UpperTheory.GalS.Nc D.nd D.naut (D.naut.lpTw (D.naut.locW i σ (D.naut.plGw k v)) ((1 - (D.R.r : ℝ)) / 2)) :=
    (UpperTheory.GalS.nc_tw _ _).2 (hL.2 k v _ hfull (by rw [← D.naut.lab_loc i k σ v]; exact (hgood k).1.2.1 v)
      (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by rw [hdim]; unfold Ranks.nV; omega)))
  have h1 := hL.1 k v _ hfull s hs hwild
  rw [hdim] at h1
  have h2 := D.naut.wdOf_ine i (mapRep (iotaOQ D.nd D.naut i) ρ) _ hw hcont s hs
  rw [e.ine hn s hs, D.naut.inePol_tw _ _ _ hs, h1] at h2
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have h3 : ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective (iotaO D.nd D.naut i)
      ((D.naut.iotaQC i).injective.comp hιi)
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, hcomp,
      ← Polynomial.map_map, ← Matrix.charpoly_map]
    exact h2
  have h4 := hT.2 i σ hocc hgood Sig ρ hP hρ s
  rw [h3, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one] at h4
  have h5 : ((D.ntypes.rbar σ (D.nd.w i) s : GL (Fin D.R.r) (Fb (D.what₂.places.resChar (D.nd.w i))
      (D.what₂.places.resChar_prime (D.nd.w i)))) : Matrix (Fin D.R.r) (Fin D.R.r)
      (Fb (D.what₂.places.resChar (D.nd.w i)) (D.what₂.places.resChar_prime (D.nd.w i)))).charpoly =
      (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective
      (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom
      (RingHom.injective _)
    rw [h4, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  have h6 : s ∈ (D.ntypes.rbar σ (D.nd.w i)).ker := by
    refine GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _ inferInstance
      (D.ntypes.rbar_open σ _) s ((D.what₂.places.resChar (D.nd.w i)) ^ D.R.r) (fun hmem => hw ?_) hwild ?_
    · rw [Nat.cast_pow, D.nd.w_l i] at hmem
      exact (D.naut.plGw k v).isPrime.mem_of_pow_mem _ hmem
    · rw [MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]
      exact GlobalTheory.TameLabels.pow_eq_one_of_charpoly _ h5
  exact h6

end GlobalTheory.RowWildTame

namespace GlobalTheory.RowTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

end GlobalTheory.RowTie
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TraceOfCharpoly
section
noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

theorem cyc_onto (D : D7) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k) (u : ℤ_[D.nd.l i]ˣ) :
    ∃ g : GE D.nd, cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g = u := by
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨w, hw⟩ := GlobalTheory.OChoose.placesOver_nonempty D.host.E (D.nd.l i) (D.nd.lPrime i).out
  have h1 : (D.nbr i w hw).Kw.1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 ((GlobalTheory.TypeDegOne.degree_one D i k hl).2 w hw)
  obtain ⟨σ, -, hσu⟩ := GlobalTheory.Cyc.exists_inertia_cycZ_eq (D.nd.l i) u
  have hσ : σ ∈ Formalism.BasicNotions.Loc.GK (D.nbr i w hw).Kw := by
    refine GlobalTheory.EpsInertia.mem_GK _ σ fun x => ?_
    have hx := (D.nbr i w hw).j_E x
    rw [h1, IntermediateField.mem_bot] at hx
    obtain ⟨q, hq⟩ := hx
    rw [← hq]; exact σ.commutes q
  refine ⟨((D.nbr i w hw).e.symm ⟨σ, hσ⟩).1, ?_⟩
  rw [GlobalTheory.EpsInertia.cycZ_bridge (D.nbr i w hw), MulEquiv.apply_symm_apply]
  exact hσu

theorem charP_res (D : D7) (i : D.nd.Loc) : CharP (IsLocalRing.ResidueField (D.nd.O i)) (D.nd.l i) := by
  have hm := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ_[D.nd.l i]) (IsLocalRing.maximalIdeal (D.nd.O i))
  have h1 : ((D.nd.l i : ℕ) : ℤ_[D.nd.l i]) ∈ (IsLocalRing.maximalIdeal (D.nd.O i)).comap (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
    rw [IsLocalRing.eq_maximalIdeal hm]
    exact PadicInt.irreducible_p.not_isUnit
  rw [Ideal.mem_comap, map_natCast, ← IsLocalRing.residue_eq_zero_iff, map_natCast] at h1
  exact (CharP.charP_iff_prime_eq_zero (D.nd.lPrime i).out).2 h1

def chiBar (D : D7) (i : D.nd.Loc) (j : Fin D.R.t) : GE D.nd →* IsLocalRing.ResidueField (D.nd.O i) :=
  (IsLocalRing.residue (D.nd.O i)).toMonoidHom.comp ((Units.coeHom _).comp (D.nd.chi i ((j : ℕ) + 1)))

theorem chiBar_inj (D : D7) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k) : Function.Injective (chiBar D i) := by
  intro j j' e
  haveI := charP_res D i
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hbig : 16 * D.R.t ^ 2 < D.nd.l i := hl ▸ DiscreteGroups.sglob.DzType.big_of_le_nV D k (by unfold Ranks.nV; omega)
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (D.nd.l i))ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hζ
  have hu : IsUnit (((ζ : ZMod (D.nd.l i)).val : ℕ) : ℤ_[D.nd.l i]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (ZMod.val_coe_unit_coprime ζ).symm
  obtain ⟨g, hg⟩ := cyc_onto D i k hl hu.unit
  let φ : (ZMod (D.nd.l i))ˣ →* (IsLocalRing.ResidueField (D.nd.O i))ˣ :=
    Units.map (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i))).toMonoidHom
  have hφ : Function.Injective φ := Units.map_injective (RingHom.injective _)
  let R : (D.nd.O i)ˣ →* (IsLocalRing.ResidueField (D.nd.O i))ˣ := Units.map (IsLocalRing.residue (D.nd.O i)).toMonoidHom
  have hy : R (Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom hu.unit) = φ ζ := by
    apply Units.ext
    show IsLocalRing.residue _ (algebraMap ℤ_[D.nd.l i] (D.nd.O i) (((ζ : ZMod (D.nd.l i)).val : ℕ) : ℤ_[D.nd.l i])) =
      ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i)) (ζ : ZMod (D.nd.l i))
    rw [map_natCast, map_natCast]
    conv_rhs => rw [← ZMod.natCast_zmod_val (ζ : ZMod (D.nd.l i)), map_natCast]
  have key : ∀ c : Fin D.R.t, R (D.nd.chi i ((c : ℕ) + 1) g) = R (D.nd.chi i 1 g) * (φ ζ ^ (c : ℕ))⁻¹ := fun c => by
    rw [D.nd.chi_def i ((c : ℕ) + 1) (by omega) (by omega), MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply,
      MonoidHom.comp_apply, hg, map_zpow, hy, ← zpow_natCast, ← zpow_neg]
    congr 2
    push_cast; ring
  have e1 : R (D.nd.chi i ((j : ℕ) + 1) g) = R (D.nd.chi i ((j' : ℕ) + 1) g) := Units.ext (DFunLike.congr_fun e g)
  rw [key, key, mul_right_inj, inv_inj, ← map_pow, ← map_pow] at e1
  have hj := j.2
  have hj' := j'.2
  exact Fin.ext (pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hζ]; have : D.R.t ≤ D.R.t ^ 2 := Nat.le_self_pow two_ne_zero _; omega)
    (by rw [Set.mem_Iio, hζ]; have : D.R.t ≤ D.R.t ^ 2 := Nat.le_self_pow two_ne_zero _; omega) (hφ e1))

theorem trace_of_charpoly {k : Type} [Field k] {a t : ℕ} (M : Matrix (Fin (a + t)) (Fin (a + t)) k) (A : Matrix (Fin a) (Fin a) k)
    (c : Fin t → k) (h : M.charpoly = A.charpoly * ∏ j, (X - C (c j))) : M.trace = A.trace + ∑ j, c j := by
  have e : M.charpoly = (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 (Matrix.diagonal c))).charpoly := by
    rw [h, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_diagonal]
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, e, ← Matrix.trace_eq_neg_charpoly_nextCoeff]
  simp [Matrix.trace, Fin.sum_univ_add]

theorem trace_sumRep {k Γ : Type} [CommRing k] [Group Γ] {a b : ℕ} (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k).trace =
      (ρ g : Matrix (Fin a) (Fin a) k).trace + (ρ' g : Matrix (Fin b) (Fin b) k).trace := by
  have e : ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl
  rw [e]
  simp [Matrix.trace, Fin.sum_univ_add]

theorem noDouble_of_live (D : D7) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k)
    (hL : GlobalTheory.CoefDuty.Live D.nd i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (hb : ResidualCharpolyIndependent D.nd i r) (x : D.nd.X i) {K' : Type} [Field K'] (f : D.nd.O i →+* K') (hf : Function.Injective f) {d u : ℕ}
    (σ : GE D.nd →* GL (Fin d) K') (υ : GE D.nd →* GL (Fin u) K') (h : d + d + u = D.R.nV) (Pm : GL (Fin D.R.nV) K')
    (hd : 0 < d)
    (hrel : ∀ g, ((Pm⁻¹ * mapRep f (r x) g * Pm : GL (Fin D.R.nV) K') : Matrix (Fin D.R.nV) (Fin D.R.nV) K') =
      Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K')) : False := by
  classical
  obtain ⟨π, -, r0, ρ0, hr0, ⟨e0, he0⟩, habs⟩ := hL
  haveI := charP_res D i
  have hbig : 16 * D.R.nV ^ 2 < D.nd.l i := hl ▸ DiscreteGroups.sglob.DzType.big_of_le_nV D k le_rfl
  have hn : D.R.nV = D.R.r + D.R.t := rfl
  have hr2 : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  refine Dbl.core f hf (IsLocalRing.residue (D.nd.O i)) IsLocalRing.residue_surjective (a := D.R.r) (t := D.R.t) hr2
    (d := d) (u := u) (by omega) ((Units.coeHom _).comp (r x)) ((Units.coeHom _).comp σ) ((Units.coeHom _).comp υ)
    ((Units.coeHom _).comp (mapRep (IsLocalRing.residue (D.nd.O i)) ρ0)) (chiBar D i) (chiBar_inj D i k hl)
    (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs) (fun g => ?_) (fun g => ?_) (fun c => ((c : ℕ) : _)) fun c c' e => ?_
  · have t := congrArg Matrix.trace (hrel g)
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at t
    have t2 : (Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K')).trace = ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K').trace :=
      Equiv.sum_comp (finCongr h).symm fun j => ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K') j j
    rw [t2, trace_sumRep, trace_sumRep, ← two_mul] at t
    exact (map_sum f _ _).trans t
  · have d0 := charpoly_of_decomp D i (fun _ => r0) (fun _ => ρ0) π ⟨e0, he0⟩ g
    have hc := charpoly_eq_of_isHeckeGalois GlobalTheory.Published.cheb_holds D i r hr π r0 hr0 g
    have e0' : (mat r0 g).charpoly = (mat ρ0 g).charpoly *
      ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i)) := d0
    have e1 : ((mat (r x) g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
        ((mat (r π) g).map (IsLocalRing.residue (D.nd.O i))).charpoly := hb x π g
    have e2 : ((mat (r x) g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
        ((mat ρ0 g).map (IsLocalRing.residue (D.nd.O i))).charpoly * ∏ j : Fin D.R.t, (X - C (chiBar D i j g)) := by
      rw [e1, Matrix.charpoly_map, hc, e0', Polynomial.map_mul, ← Matrix.charpoly_map, Polynomial.map_prod]
      congr 1
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, Finset.prod_range]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Polynomial.map_sub, map_X, map_C, add_comm 1]
      rfl
    exact (map_sum (IsLocalRing.residue (D.nd.O i)) _ _).trans (trace_of_charpoly (a := D.R.r) (t := D.R.t) _ _ _ e2)
  · have h1 := c.2
    have h2 := c'.2
    have h3 : D.R.nV ≤ D.R.nV ^ 2 := Nat.le_self_pow two_ne_zero _
    exact Fin.ext (CharP.natCast_injOn_Iio (IsLocalRing.ResidueField (D.nd.O i)) (D.nd.l i)
      (by rw [Set.mem_Iio]; omega) (by rw [Set.mem_Iio]; omega) e)

end UpperTheory.GalS
end
end

