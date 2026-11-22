import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.LocalToGlobal.NumberFieldFamilies.IsLocalizedOfSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0780
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0368
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0793
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0792
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0741
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0718
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0635
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOnThetaPtNatural
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0782
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0585
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalEigenData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocN

set_option synthInstance.maxHeartbeats 400000

def feSup {l : ℕ} [Fact l.Prime] (K L : Loc.FinExt l) : Loc.FinExt l :=
  ⟨K.1 ⊔ L.1, haveI := K.2; haveI := L.2; IntermediateField.finiteDimensional_sup _ _⟩

theorem osInt (D : D7) (B : LocBase0 D.host D.what₂) : OsInt B := fun j w y =>
  IsIntegrallyClosed.isIntegral_iff.1 <| by
    obtain ⟨p, hp, h0⟩ := D.O_int y
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [eval₂_map, Subsingleton.elim (RingHom.comp _ _) ((B.ec j w).comp (algebraMap ℤ D.what₂.LL)), ← hom_eval₂, h0, map_zero]

theorem plGwDisj (D : D7) : PlGwDisj D := by
  have key : ∀ v v', D.naut.plGw 0 v ≠ D.naut.plGw 1 v' := fun v v' e => by
    have h0 : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw 0 v).asIdeal := D.naut.plGw_over 0 v
    have h1 : ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw 1 v').asIdeal := D.naut.plGw_over 1 v'
    rw [← e] at h1
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
      ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne).cast
    exact (D.naut.plGw 0 v).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)))
  intro k k' v v' e
  fin_cases k <;> fin_cases k'
  · rfl
  · exact absurd e (key v v')
  · exact absurd e.symm (key v' v)
  · rfl

section Psi

variable {D : D7} {C : NChoice D} {X : CoefIn D.what₂} {ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)}
  (hψ0 : ∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) =
    algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w))))
  (hP : PsiInt X ψ0) (j : ℕ) (w : D.what₂.places.Pl)

theorem psN_spec (g : G D.host.E D.nd.Om) : algebraMap (OcC X j w) (FractionRing (OcC X j w)) (psN X ψ0 hP j w g : OcC X j w) =
    ecC X j w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
  unitsLift_spec ((Units.map (ecC X j w).toMonoidHom).comp (ψ0 w)) (hP j w) g

include hψ0 in

theorem psN_eq_one (g : G D.host.E D.nd.Om) : psN X ψ0 hP j w g = 1 ↔ ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) g = 1 := by
  rw [← Units.val_eq_one, ← map_eq_one_iff _ (IsFractionRing.injective (OcC X j w) (FractionRing (OcC X j w))), psN_spec,
    map_eq_one_iff _ (ecC X j w).injective, ← map_eq_one_iff _ (C.embW w).injective, hψ0,
    map_eq_one_iff _ (IsFractionRing.injective (C.Oe w) (FractionRing (C.Oe w))), map_eq_one_iff _ (C.Oe_inj w),
    Units.val_eq_one]
  rfl

include hψ0 in
theorem psN_of_art {g : G D.host.E D.nd.Om} (h : D.ntw.art (C.twI w) (C.Q w) g = 1) : psN X ψ0 hP j w g = 1 := by
  rw [psN_eq_one hψ0, MonoidHom.comp_apply, h, map_one]

include hψ0 in
theorem psN_ord (g : G D.host.E D.nd.Om) : ∃ n : ℕ, psN X ψ0 hP j w g ^ (D.what₂.places.resChar w ^ n) = 1 := by
  obtain ⟨n, hn⟩ := D.ntw.RCG_l _ _ (D.ntw.art (C.twI w) (C.Q w) g)
  rw [C.twI_l, ← map_pow] at hn
  exact ⟨n, by rw [← map_pow]; exact psN_of_art hψ0 hP j w hn⟩

include hψ0 in
theorem psN_open : IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om)) :=
  Subgroup.isOpen_mono (H₁ := (D.ntw.art (C.twI w) (C.Q w)).ker) (fun _ hg => psN_of_art hψ0 hP j w hg) (D.ntw.art_cont _ _)

include hψ0 in
theorem psN_anti : AntiHom D.ntw.cc (psN X ψ0 hP j w) := fun g g' h => by
  rw [eq_inv_iff_mul_eq_one, ← map_mul]
  exact psN_of_art hψ0 hP j w (by rw [map_mul, D.ntw.art_anti _ _ g g' h, inv_mul_cancel])

include hψ0 in
theorem psN_ram (h : ∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) :
    RamExactly (psN X ψ0 hP j w) (↑(C.Q w) : Set (HeightOneSpectrum (𝓞 D.host.E))) := fun v A hA => by
  constructor
  · rintro ⟨σ, hσ, hne⟩
    by_contra hv
    exact hne (psN_of_art hψ0 hP j w (D.ntw.art_unr _ _ v hv A hA σ hσ))
  · intro hv
    obtain ⟨σ, hσ, hne⟩ := h v hv A hA
    exact ⟨σ, hσ, fun e => hne ((psN_eq_one hψ0 hP j w σ).1 e)⟩

end Psi

set_option maxHeartbeats 2000000 in

theorem ndSpec_exists : GlobalTheory.Published.GlobalArtinReciprocity → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (X : LocNd (lay0 D)) (T : LocTw X), Nonempty (NdSpec A.pl M C big X T) := by
  intro hArt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI _ _ hpd hCheb hOS hVal big
  obtain ⟨hO, hc⟩ := GlobalTheory.T.twistConductors_over_real_places_and_conj_stable D cf C tp hCS.off
  have hG := GlobalTheory.T.heckeGeneratorPlacesOutsideLevel_of_stable D cf M C tp hMI hO
  have hX := GlobalTheory.T.exists_conjugate_splitPlace_and_uniformizer D
  have hR := GlobalTheory.T.exists_coefficientLinear_lift_doubleCosetOperators D M C tp.tup hStd hG hMI
  have hCm := GlobalTheory.T.liftedHeckeOperators_at_generators_commute D M C hR hStd hG hX
  choose F1 hF1 using GlobalTheory.T.exists_padicFiniteExt_containing_all_hecke_eigenvalues D M C hR (plEmb A.pl) hCm
  choose F2 hF2 hF2' using GlobalTheory.T.exists_padicFiniteExt_containing_coeffField_and_numbers D A.pl big
  choose F3 hF3 using GlobalTheory.T.localBridges_at_placesOverResidueChar_of_large_coeff D
  choose F4 hF4 using GlobalTheory.T.exists_twist_ring_map_large_coefficient_rings D C Bs.twF low (plEmb A.pl) Bs.tw hCS.choice
  obtain ⟨X, hXE, h1, h2, h3, h4⟩ : ∃ X : CoefIn D.what₂, X.E = plEmb A.pl ∧ (∀ j w, (F1 j w).1 ≤ (X.Kx j w).1) ∧
      (∀ j w, (F2 w).1 ≤ (X.Kx j w).1) ∧ (∀ j w, (F3 w).1 ≤ (X.Kx j w).1) ∧ ∀ j w, (F4 w).1 ≤ (X.Kx j w).1 :=
    ⟨coefIn A.pl (fun j w => feSup (feSup (F1 j w) (F2 w)) (feSup (F3 w) (F4 w)))
      (fun j w x => (le_sup_of_le_left le_sup_right : (F2 w).1 ≤ ((F1 j w).1 ⊔ (F2 w).1) ⊔ ((F3 w).1 ⊔ (F4 w).1)) (hF2 w x)), rfl,
      fun _ _ => le_sup_of_le_left le_sup_left, fun _ _ => le_sup_of_le_left le_sup_right,
      fun _ _ => le_sup_of_le_right le_sup_left, fun _ _ => le_sup_of_le_right le_sup_right⟩
  have hS : SplitK (mt0 M) C.Q hR X := fun j w => hF1 j w X hXE (h1 j w)
  choose twC hTwA hTwR hTwE using fun j w => hF4 w X j hXE (h4 j w)
  obtain ⟨ψ0, -, hψ0, -⟩ := hCS.nct.psi_eq
  have hP := GlobalTheory.T.twistCharacterValues_integral_units_at_place D C X ψ0 hψ0
  have hs := GlobalTheory.T.heckeStandardFacts_on_localisation_base D M C hR X hS hStd hG hX hCm
  have hd := GlobalTheory.T.finiteDimensional_localisation_space_all (base M C hR X hS)
  have hML := LatticeFinitenessFree.mtLoc_holds (partCompl_of hs hd)
  have hAct := GlobalTheory.T.heckeRing_acts_faithfully_on_localisedLattice _ hs hd hML (GlobalTheory.T.heckeOperator_integral_on_lattice_at_twisted_places D M C hR X hS tp.tup hMI hX)
    (GlobalTheory.T.heckeOperators_on_localisation_space_semisimple D M C hR X hS hStd GlobalTheory.T.splitPlace_doubleCosetOperator_semisimple_typeSpace hG hX)
  have hAHK := GlobalTheory.T.heckeRing_acts_on_lattice_as_operators _ hs hd hML hAct
  have hI := osInt D (base M C hR X hS)
  have hGal := fun w (hw : TwistedAt D w) => GlobalTheory.T.twistCharacter_ramified_at_conductor_trivial_above_l D cf C tp w hArt hCheb hCS.psi hw (hVal w hw) (hCS.adm w hw)
  have htw : ∀ w v, v ∈ C.Q w → TwistedAt D w := fun w v hv => by
    by_contra hw
    rw [hCS.off w hw] at hv
    exact absurd hv (Finset.notMem_empty v)
  have hQl : ∀ w v, v ∈ C.Q w → v ∉ placesOver D.host.E (D.what₂.places.resChar w) := fun w v hv =>
    C.twI_l w ▸ ((hCS.adm w (htw w v hv)).1 v hv).2
  have hQS : ∀ w v, v ∈ C.Q w → v ∉ exceptionalPlaces D.host (D.what₂.places.resChar w) := fun w v hv h => by
    have ha := (hCS.adm w (htw w v hv)).2.1 v hv
    rcases h.1 with h | h | h
    · exact ha.2 0 h
    · exact ha.2 1 h
    · refine ha.1 (Finset.mem_coe.1 ?_)
      rw [D.ntw.pD_eq, C.twI_l]
      exact h
  have hSs : ∀ l v, v ∈ exceptionalPlaces D.host l → IsSplitPl D.host v := fun l v h => by
    rcases h.1 with h | h | h
    · exact GlobalTheory.T.typePrime_places_isSplitPlace D 0 v h
    · exact GlobalTheory.T.typePrime_places_isSplitPlace D 1 v h
    · split_ifs at h
      · exact hpd v (Or.inr h)
      · exact hpd v (Or.inl h)
  have hRP := fun j w (hw : TwistedAt D w) => psN_ram hψ0 hP j w (hGal w hw).1
  refine ⟨_, _, nonempty_spec (base M C hR X hS) C hs hd hML (LatticeFinitenessFree.mtSub_free _) (LatticeFinitenessFree.mtSub_finite _) (GlobalTheory.T.localisation_heckeRing_isLocalRing _ hs hd) hAct
    (GlobalTheory.T.heckeEigenspace_ne_bot_every_localisation_point _ hs hd hML hAct hAHK) (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i))
    (GlobalTheory.T.localisation_galoisCharacter_continuous D M C hR X hS twC ψ0 hP hTwA (psN_open hψ0 hP))
    (fun i v hv => hv.elim (fun h => hSs _ v ((Set.Finite.mem_toFinset _).1 h))
      (fun h => ((hCS.adm _ (htw _ v h)).1 v h).1))
    (fun i => Finset.disjoint_left.2 fun v h h' => hQS _ v h' ((Set.Finite.mem_toFinset _).1 h)) hQl ?_ hI
    (GlobalTheory.T.latticeBaseChange_free_over_localisation_coeffRing D _ hI hOS) (fun a => hTwE _ _ a.2.2.2.2.2) (fun a => psN_ord hψ0 hP _ _) (fun a => psN_open hψ0 hP _ _)
    (fun a => psN_anti hψ0 hP _ _) (fun a => hRP _ _ a.2.2.2.2.2)
    (fun a v hv B hB σ hσ => (psN_eq_one hψ0 hP _ _ σ).2 ((hGal _ a.2.2.2.2.2).2 v hv B hB σ hσ))
    A.pl M big (fun j w h1 h2 v k s ϖ hg hcj hu x => hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hcj hu x) hO hc
    (fun _ => rfl) (iqC X) (fun j w z => (iqC_alg X j w _).trans rfl) ?_ ?_ hAHK (plGwDisj D) ?_ (fun a => hTwA _ _)
    (fun a => hTwR _ _) (fun j w => hF3 w X j (h3 j w))⟩
  · intro i v hv
    have hw : TwistedAt D (wOf _ i) := i.2.2.2.2.2
    obtain ⟨σ, hσ, hne⟩ := (hRP (jOf _ i) _ hw v _ (D.nd.plOm.2 v)).2 hv
    have ha := hCS.adm _ hw
    have h1 := D.ntw.twistCharacterFamily_unramified (C.twI (wOf _ i)) (jOf _ i) (C.sd (wOf _ i)) v (ha.1 v hv).2 (ha.2.1 v hv).2 (ha.2.1 v hv).1 _
      (D.nd.plOm.2 v) σ hσ
    refine ⟨σ, hσ, fun e => hne ?_⟩
    have e' : Units.map (twC (jOf _ i) (wOf _ i)).toMonoidHom (D.ntw.chi1 (C.twI (wOf _ i)) (jOf _ i) (C.sd (wOf _ i)) σ) *
        psN X ψ0 hP (jOf _ i) (wOf _ i) σ = 1 := e
    rwa [h1, map_one, one_mul] at e'
  · intro j w x
    change A.pl.ι w (iqC X j w (ecC X j w x)) = _
    rw [iqC_ec, hXE]
    exact (A.pl.ι w).apply_symm_apply _
  · intro j w z hz
    obtain ⟨x, hx⟩ := iqC_surj X j w _ (h2 j w (hF2' w z hz))
    exact ⟨x, (congrArg (A.pl.ι w) hx).trans ((A.pl.ι w).apply_symm_apply z)⟩
  · intro a g y hy
    obtain rfl := (C.embW _).injective (hy.trans (hψ0 _ g).symm)
    exact (psN_spec hP _ _ g).symm

end GlobalTheory.HeckeLocN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionFunctionLinearOnCellsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_function_linearOn_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (K D : ℕ), IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (starFun H.bar ψ w K D).LinearOn γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (starFun H.bar ψ w K D).LinearOn (Fin.cons β₀ fun j => γ (s j))) := by
  first | exact @GlobalTheory.PolFan.starFun_linearOn | exact GlobalTheory.PolFan.starFun_linearOn | (intros; apply GlobalTheory.PolFan.starFun_linearOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem bc_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'')
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ w = spMap (dualMap (ψ.comp φ)) ≫ w := by
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Formalism.L2.Pj.dualMap_comp]

theorem isTanBasis_map {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : GlobalTheory.LineNorm.IsTanBasis t x e) (φ : R →+* S) :
    GlobalTheory.LineNorm.IsTanBasis t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) := by
  refine ⟨fun i => GlobalTheory.FactorDepth.isTanAtG_map t φ (h.1 i), fun T _ ψ w hw => ?_⟩
  simp only [bc_bc]
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap] at hw ⊢
  exact h.2 T (ψ.comp φ) w hw

theorem ext_uniq (hX : X.IsSeparated) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    (x y : Sp ↥(intO C) ⟶ X) (h : spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ x) : y = x := by
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

theorem mem_latDR_iff (hX : X.IsSeparated) {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : GlobalTheory.LineNorm.IsTanBasis t x e) (C : Type)
    [NontriviallyNormedField C] [IsUltrametricDist C] (φ : R →+* ↥(intO C)) (cf : Fin g → C)
    (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (fun i => spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) cf w) :
    w ∈ latDR t (spMap (intO C).subtype ≫ spMap φ ≫ x) ↔ ∀ i, ‖cf i‖ ≤ 1 := by
  have hb := isTanBasis_map t he φ
  have hv : ∀ i, IsTanAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) := fun i => by
    rw [← bc_bc]; exact GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (hb.1 i)
  have hxC : spMap (intO C).subtype ≫ spMap φ ≫ x = spMap ((intO C).subtype.comp φ) ≫ x := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  constructor
  · rintro ⟨xO, hx, vO, hvO, rfl⟩ i
    obtain rfl := ext_uniq hX C _ _ hx
    obtain ⟨a, ha, -⟩ := he.2 (↥(intO C)) φ vO hvO
    have hc := GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha
    simp only [bc_bc] at hc
    have ht := GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype hvO
    rw [hxC] at ht hc hw
    have e1 := (he.2 C _ _ ht).unique hw hc
    rw [e1]
    exact (a i).2
  · intro hc
    obtain ⟨wO, hwO, hcO⟩ := GlobalTheory.FlagEmb.exists_comb t hb.1 fun i => (⟨cf i, hc i⟩ : ↥(intO C))
    refine ⟨_, rfl, wO, hwO, ?_⟩
    have hb' := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [bc_bc] at hb'
    exact GlobalTheory.FlagEmb.comb_unique t hv hb' hw

theorem sum_single {R C : Type} [CommRing R] [NontriviallyNormedField C] [IsUltrametricDist C] {g : ℕ}
    (φ : R →+* ↥(intO C)) (i : Fin g) (a : R) (cf : Fin g → C) :
    ∑ k, ((φ ((Pi.single i a : Fin g → R) k) : ↥(intO C)) : C) * cf k = (φ a : C) * cf i := by
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
  simp

end GlobalTheory.HTPres

namespace GlobalTheory.HTPres

theorem exists_pres : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) [IsLocallyNoetherian X], X.IsSeparated → ∀ (p : ℕ), p.Prime → ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ X), (∃ ζ : R, IsPrimitiveRoot ζ p) → GlobalTheory.LineNorm.SplitTors t x p → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), GlobalTheory.LineNorm.IsTanBasis t x e → ∀ b : Bool, ∃ (M : ℕ) (h : Fin (M + 1) → Fin g → R), Pres t x p b e h := by
  intro hB E _ _ _ H X t _ hX p hp R _ _ _ _ x hζ hS g e he b
  cases b with
  | false =>
    refine ⟨g, Fin.cons 0 (fun i => Pi.single i 1), ⟨0, fun i => ?_⟩, fun C φ cf w hw => ?_⟩
    · rw [pow_zero]
      exact Submodule.subset_span ⟨i.succ, by simp⟩
    · change w ∈ latDR t _ ↔ _
      rw [mem_latDR_iff t hX x he C.S φ cf w hw, Fin.forall_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, sum_single, map_one]
      simp
  | true =>
    obtain ⟨n, h', hh'⟩ := GlobalTheory.T.exists_tangent_presentation_prime E H X t R x g e he p hp hζ hS
    refine ⟨n + g, Fin.cons 0 (Fin.append h' fun i => Pi.single i (p : R)), ⟨1, fun i => ?_⟩, fun C φ cf w hw => ?_⟩
    · rw [pow_one]
      exact Submodule.subset_span ⟨(Fin.natAdd n i).succ, by simp⟩
    · haveI := Fact.mk hp
      have hw' : IsCombAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x)
          (fun i => spMap (dualMap (intO ↥C.S).subtype) ≫ spMap (dualMap φ) ≫ e i) cf w := by
        simpa only [bc_bc] using hw
      change w ∈ latHT t p _ ↔ _
      rw [GlobalTheory.T.unique_integral_lift_norm_p_inverse hB E H X t p ↥C.S C.norm_p (spMap φ ≫ x)
        (fun x' hx' => ext_uniq hX _ _ _ hx') g _ (isTanBasis_map t he φ) n (fun j i => φ (h' j i))
        (hh' ↥C.S φ).1 (hh' ↥C.S φ).2 cf w hw', Fin.forall_fin_succ, Fin.forall_fin_add]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.append_left, Fin.append_right, sum_single, map_natCast]
      simp [norm_mul]

end GlobalTheory.HTPres
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoPowMulExp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tendsto_pow_mul_exp (C C' c c' T : ℝ) (B : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    Tendsto (fun w : ℂ => C * Real.exp (-c * (c' * (w.im - T))) * (C' * w.im ^ B)) imTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => t ^ B * Real.exp (-(c * c') * t)) atTop (𝓝 0) := by
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (B : ℝ) (c * c') (mul_pos hc hc')
    simpa only [Real.rpow_natCast] using this
  have h2 := (h1.const_mul (C * C' * Real.exp (c * c' * T))).comp (tendsto_comap (f := Complex.im))
  rw [mul_zero] at h2
  refine h2.congr fun w => ?_
  have : Real.exp (-c * (c' * (w.im - T))) = Real.exp (c * c' * T) * Real.exp (-(c * c') * w.im) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [Function.comp, this]
  ring

theorem tendsto_cusp {N : ℕ} {X : Data E N} {T : ℝ} {x : ℂ → Frame X.Ψ N} {la : Wt X.Ψ N} {P : Frame X.Ψ N → ℂ}
    (hP : P ∈ X.SS la) (hd : ∀ w : ℂ, T < w.im → x w ∈ X.dom) {ξ : Fin N → E} {c' : ℝ} (hξ : X.IsIso ξ) (hc' : 0 < c')
    (ht : ∀ w : ℂ, T + 1 < w.im → ∀ τ, c' * (w.im - T) ≤ X.tt ξ (x w) τ) {C' : ℝ} {B : ℕ}
    (hn : ∀ᶠ w in imTop, 0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ C' * w.im ^ B) :
    Tendsto (fun w => P (x w)) imTop (𝓝 0) := by
  obtain ⟨C, c, hc, hC⟩ := GlobalTheory.T.pnorm_le_exp_neg_of_mem_SS_of_isIso E N X la P ξ hP hξ
  refine squeeze_zero_norm' ?_ (tendsto_pow_mul_exp C C' c c' T B hc hc')
  have he : ∀ᶠ w in imTop, T + 1 + 1 / c' < w.im :=
    (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop _)
  filter_upwards [hn, he] with w h1 h2
  have h0 : 0 < 1 / c' := by positivity
  have h3 : 1 ≤ c' * (w.im - T) := by
    have : 1 / c' ≤ w.im - T := by linarith
    rwa [div_le_iff₀' hc'] at this
  have h4 := hC (x w) (hd w (by linarith)) _ h3 (ht w (by linarith))
  have h5 : ‖P (x w)‖ = X.pnorm la P (x w) * (X.nfac la (x w))⁻¹ := by
    show _ = ‖P (x w)‖ * X.nfac la (x w) * _
    rw [mul_assoc, mul_inv_cancel₀ h1.1.ne', mul_one]
  have h6 : 0 ≤ X.pnorm la P (x w) := mul_nonneg (norm_nonneg _) h1.1.le
  rw [h5]
  exact mul_le_mul h4 h1.2 (inv_nonneg.2 h1.1.le) (h6.trans h4)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type}
  [CommRing O] {β : O →+* c.F}

theorem isEqn_LEx {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) (ex : Ix Dw → ℤ) {y : C.Y.X}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ} (ht : ∀ τ i, (C.gr τ i).IsEqn y (t τ i)) :
    (C.LEx ex).IsEqn y (∏ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t k.1 k.2 ^ ex (some k))⁻¹ := by
  have hE : ∀ s : Finset (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      (∑ k ∈ s, ex (some k) • C.gr k.1 k.2).IsEqn y (∏ k ∈ s, t k.1 k.2 ^ ex (some k)) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero y
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk]; exact ((ht _ _).zsmul _).add ih
  exact (hE Finset.univ).neg

end GlobalTheory.ShFam.BdArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsChainDataWithBasePoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 4000000 in

theorem tw_ties_with_points : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F), Formalism.L2.Herm.TwChMu0 T ∧ I.StdW l Z l0 W ∧ Nonempty (SymmetricTwistedJointForms T F) ∧
    (∀ u a (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m), ∃ k, I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
      (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
      (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
      (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)) := by
  intro B X I hI hP l Z l0 inQ H F hQ hF hH
  obtain ⟨T, J, W, h0, hW, hJ⟩ := GlobalTheory.T.trueColumnChoice_twistedChains_formsClasses I hI hP l Z l0 inQ H F hQ hF hH (fun u => (hF u).2.2)
  exact ⟨T, J, W, h0, hW, hJ, fun u a ha h1 => hW.topk u a ha h1⟩

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceLocalIndexStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_place_local_index : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → ∃ i : (w.D Z).nd.Loc, (w.D Z).nd.w i = v ∧ (w.D Z).nd.j i = j := by
  first | exact @GlobalTheory.HeightCounting.Up.LocEx.exists_loc | exact GlobalTheory.HeightCounting.Up.LocEx.exists_loc | (intros; apply GlobalTheory.HeightCounting.Up.LocEx.exists_loc <;> assumption)
end

