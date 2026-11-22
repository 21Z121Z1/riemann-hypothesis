import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeFrameCoverLevelMapsReductions
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU)
open GlobalTheory.LevPull (CongMod)
open scoped TensorProduct Matrix

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TypeFrameCover

open GlobalTheory.LevDesc

section Primes

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}

theorem typePrime_isPrime {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) (v : Sq D.host) :
    (typePrime l v).IsPrime := by
  refine halfPrime_isPrime l v.2.1.isMaximal ?_
  obtain ⟨k, hk⟩ := g_dvd (D := D) v.1
  rw [hM, hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ v.2.2

theorem typePrime_eq {l l₂ : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) (hl₂ : IsTypeLevel l₂)
    (hle : l₂.Mb ≤ l.Mb) (v : Sq D.host) : typePrime l₂ v = typePrime l v := by
  obtain ⟨hP, hN⟩ := hl₂.typePrime_spec v
  have hne : typePrime l₂ v ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hN
    exact (D.host.g_prime v.1).ne_zero hN.symm
  exact (hP.isMaximal hne).eq_of_le (typePrime_isPrime hM v).ne_top (sup_le_sup_right hle _)

theorem exists_mem_eq {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal) (v : Sq D.host) : ∃ PP ∈ Pg, PP.asIdeal = typePrime l v := by
  have hP := typePrime_isPrime hM v
  have h1 : ∏ PP ∈ Pg, PP.asIdeal ≤ typePrime l v := hMb ▸ le_sup_left
  obtain ⟨PP, hPP, h2⟩ := (hP.prod_le).1 h1
  exact ⟨PP, hPP, PP.isMaximal.eq_of_le hP.ne_top h2⟩

theorem exists_equiv {l : Level H} (hM : l.M = D.host.g 0 * D.host.g 1) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hMb : l.Mb = ∏ PP ∈ Pg, PP.asIdeal) : ∃ e : Sq D.host ≃ Pg, ∀ v, (e v).1.asIdeal = typePrime l v := by
  choose f hf hfe using exists_mem_eq hM hMb
  have hinj : Function.Injective (fun v ↦ (⟨f v, hf v⟩ : Pg)) := by
    intro v w h
    have h' : typePrime l v = typePrime l w := by
      rw [← hfe v, ← hfe w]; exact congrArg (fun x : Pg ↦ x.1.asIdeal) h
    by_contra hvw
    have hc := typePrime_coprime (l := l) hvw
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq, h', sup_idem] at hc
    exact (typePrime_isPrime hM w).ne_top hc
  have hsurj : Function.Surjective (fun v ↦ (⟨f v, hf v⟩ : Pg)) := by
    rintro ⟨PP, hPP⟩
    have hle : l.Mb ≤ PP.asIdeal := hMb ▸ Ideal.prod_le_inf.trans (Finset.inf_le hPP)
    have hm : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← Nat.cast_mul, ← hM]; exact hle (natCast_M_mem l)
    have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rcases PP.isPrime.mem_or_mem hm with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) PP.asIdeal := by
      rw [Ideal.mem_comap, map_natCast]; exact hk
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F) :=
      ⟨Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) PP.asIdeal, inferInstance, fun e ↦ by
        rw [e, Ideal.mem_bot] at hg
        exact (D.host.g_prime k).ne_zero (by exact_mod_cast hg)⟩
    have he : typePrime l ⟨k, ⟨w, hg⟩⟩ = PP.asIdeal :=
      halfPrime_eq l w.isMaximal PP.isPrime (sup_le hle Ideal.map_comap_le)
    refine ⟨⟨k, ⟨w, hg⟩⟩, Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext ?_)⟩
    exact (hfe _).trans he
  exact ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun v ↦ hfe v⟩

theorem nonempty_iso {l₂ : Level H} (hl₂ : IsTypeLevel l₂) (v : Sq D.host) (PP : Formalism.L2.DIV.Pl D.host.E)
    (hPP : PP.asIdeal = typePrime l₂ v) : Nonempty (ZMod (D.host.g v.1) ≃+* kP PP) := by
  have hc : Nat.card (kP PP) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, ← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Fintype.ofFinite (kP PP)
  exact ⟨ZMod.ringEquivOfPrime (kP PP) (D.host.g_prime v.1) (by rw [← Nat.card_eq_fintype_card, hc])⟩

end Primes

section Frame

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem exists_frame {l₂ : Level H} (hl₂ : IsTypeLevel l₂) (hr : Dw.p + Dw.q = D.R.r) (v : Sq D.host)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP.asIdeal = typePrime l₂ v) (iso : ZMod (D.host.g v.1) ≃+* kP PP)
    {n : ℕ} (hn : n = D.R.r) (φ : Dw.La →ₗ[𝓞 D.host.E] (Fin n → kP PP)) (hφ : Function.Surjective φ) :
    ∃ f : QMod Dw.La (typePrime l₂ v) ≃+ (Fin D.R.r → ZMod (D.host.g v.1)),
      ∀ x : Dw.La, f (Submodule.Quotient.mk x) = fun j ↦ iso.symm (φ x (Fin.cast hn.symm j)) := by
  subst hn
  have hker : typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) ≤ LinearMap.ker φ := by
    rw [← hPP, Submodule.smul_le]
    intro a ha x _
    rw [LinearMap.mem_ker, map_smul]
    funext j
    rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  let ψ := (typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).liftQ φ hker
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hc : Nat.card (𝓞 D.host.E ⧸ typePrime l₂ v) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ typePrime l₂ v) := Nat.finite_of_card_ne_zero (hc ▸ (D.host.g_prime _).ne_zero)
  haveI := Dw.fin
  haveI := Dw.proj
  have hN : Nat.card (QMod Dw.La (typePrime l₂ v)) = D.host.g v.1 ^ D.R.r := by
    rw [GlobalTheory.natCard_quot_smul_top_of_projective, hc, Dw.rank, hr]
  have hc' : Nat.card (kP PP) = D.host.g v.1 := by
    rw [← (hl₂.typePrime_spec v).2, ← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN' : Nat.card (Fin D.R.r → kP PP) = D.host.g v.1 ^ D.R.r := by
    rw [Nat.card_fun, hc', Nat.card_eq_fintype_card, Fintype.card_fin]
  haveI : Finite (QMod Dw.La (typePrime l₂ v)) :=
    Nat.finite_of_card_ne_zero (by rw [hN]; exact pow_ne_zero _ (D.host.g_prime _).ne_zero)
  have hψb : Function.Bijective ψ := hψs.bijective_of_nat_card_le (by rw [hN, hN'])
  let e1 : QMod Dw.La (typePrime l₂ v) ≃+ (Fin D.R.r → kP PP) := AddEquiv.ofBijective ψ.toAddMonoidHom hψb
  let e2 : (Fin D.R.r → kP PP) ≃+ (Fin D.R.r → ZMod (D.host.g v.1)) :=
    AddEquiv.piCongrRight (fun _ ↦ iso.symm.toAddEquiv)
  exact ⟨e1.trans e2, fun x ↦ rfl⟩

end Frame

section Main

theorem mulVec_reindex {K : Type} [CommRing K] {n r : ℕ} (h : n = r) (hr : r ≤ n) (Mn : Matrix (Fin n) (Fin n) K)
    (y z : Fin n → K)
    (hyz : (fun j ↦ y (Fin.cast h.symm j)) = Mn.submatrix (Fin.castLE hr) (Fin.castLE hr) *ᵥ fun j ↦ z (Fin.cast h.symm j)) :
    y = Mn *ᵥ z := by
  subst h
  exact hyz

theorem typeFrame_cover : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m), IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 → ∀ (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l l₂ : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → Dw.p + Dw.q = D.R.r → l.A = 1 → l.M = D.host.g 0 * D.host.g 1 → IsTypeLevel l₂ → l₂.Mb ≤ l.Mb → l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∀ lev : G → Dw.La →ₗ[𝓞 D.host.E] Dw.La, LevIs R i ι l.M (Mfr l) lev → ∃ (fr : TypeFrame Dw l₂) (e : Sq D.host ≃ R.Pg) (iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1), (∀ (γ : LevelAut Dw l₂) (g : G), (∀ v, R.eG g (e v) = Formalism.UG.bc (iso v : ZMod (D.host.g v.1) →+* kP (e v).1) (typeRed fr γ v)) → CongMod l.Mb (liftLa γ) (lev g)) ∧ ∀ γ : LevelAut Dw l₂, CongMod l.Mb (liftLa γ) LinearMap.id → typeRed fr γ = 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i hβ H Dw l l₂ ι hι hr hA hM hl₂ hle hMb lev hlev
  obtain ⟨e, he⟩ := exists_equiv hM hMb
  have htp : ∀ v, typePrime l₂ v = typePrime l v := typePrime_eq hM hl₂ hle
  have he₂ : ∀ v, (e v).1.asIdeal = typePrime l₂ v := fun v ↦ (he v).trans (htp v).symm
  let iso : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (e v).1 := fun v ↦ (nonempty_iso hl₂ v _ (he₂ v)).some
  have hφ := fun v : Sq D.host ↦ GlobalTheory.T.lattice_coordinates_mod_prime_selfDual_stabilizer D (Wc D i) (R.βW i) (R.ΛW i) hβ Dw.La ι hι (e v).1
  choose φ hφs hφk using hφ
  have hfr0 := fun v ↦ exists_frame hl₂ hr v (e v).1 (he₂ v) (iso v) (rank_Wc i) (φ v) (hφs v)
  choose fr hfr using hfr0
  refine ⟨fr, e, iso, ?_, ?_⟩
  · intro γ g hg a
    obtain ⟨κ, hκ, hκa⟩ := hlev g
    have hSt : Lev.finE (Wc D i) κ ∈ St (R.βW i) := parLev_St hκ.2.1
    have hin : ∀ v, l.Mb ≤ (e v).1.asIdeal := fun v ↦ by rw [he v]; exact le_sup_left
    have hkill : ∀ v, ∀ u ∈ l.Mb, ∀ x : Dw.La, φ v (u • x) = 0 := by
      intro v u hu x
      rw [map_smul]
      funext j
      rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 (hin v hu), zero_mul]
    have hcop : l.Mb ⊔ Mfr l = ⊤ := l.coprime
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l)
    have ha : a = u • a + w • a := by rw [← add_smul, huw, one_smul]
    have hlevφ : ∀ v, φ v (lev g a) = (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ)).1 *ᵥ φ v a := by
      intro v
      have h1 := hφk v κ hSt l.M (hin v (natCast_M_mem l)) (w • a) (lev g (w • a))
        (hκa (w • a) (Submodule.smul_mem_smul hw Submodule.mem_top))
      have h2 : φ v (w • a) = φ v a := by
        conv_rhs => rw [ha]
        rw [map_add, hkill v u hu, zero_add]
      have h3 : φ v (lev g a) = φ v (lev g (w • a)) := by
        conv_lhs => rw [ha]
        rw [map_add, map_add, map_smul, hkill v u hu, zero_add]
      rw [h3, h1, h2]
    have hliftφ : ∀ v, φ v (liftLa γ a) = φ v (lev g a) := by
      intro v
      have hγa : γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (liftLa γ a) := (liftLa_spec γ a).symm
      have h0 : (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) *ᵥ
          fr v (Submodule.Quotient.mk a) = fr v (Submodule.Quotient.mk (liftLa γ a)) := by
        have h00 := GlobalTheory.LevDesc.typeRed_mulVec fr γ v (Submodule.Quotient.mk a)
        rw [hγa] at h00
        exact h00
      rw [hfr, hfr] at h0
      have h1 := GlobalTheory.LevelActionPinned.equiv_mulVec (iso v)
        (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1)))
        (fun j ↦ (iso v).symm (φ v a (Fin.cast (rank_Wc i).symm j)))
      rw [h0] at h1
      simp only [RingEquiv.apply_symm_apply] at h1
      have hT : (typeRed fr γ v : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))).map (iso v) =
          (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ) : Matrix _ _ _).submatrix
            (Fin.castLE (R.datWp i R.triv).hr) (Fin.castLE (R.datWp i R.triv).hr) := by
        have h5 : R.eG g (e v) = upperLeftBlock (R.datWp i R.triv).hr (redFn (R.βW i) (e v).1 (Lev.finE (Wc D i) κ)) :=
          (congrFun hκ.2.2 (e v)).symm
        have h6 := upper_block_val_submatrix (R.datWp i R.triv).hr (blockTri_blkOf_le _ _ (parLev_g hκ.2.1 (e v).2))
        rw [← h5, hg v] at h6
        exact h6
      rw [hT] at h1
      rw [hlevφ v]
      exact mulVec_reindex (rank_Wc i) _ _ _ _ h1
    have hall : ∀ v, liftLa γ a - lev g a ∈ typePrime l v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
      intro v
      have hx : φ v (liftLa γ a - lev g a) = 0 := by rw [map_sub, sub_eq_zero, hliftφ v]
      have h4 : fr v (Submodule.Quotient.mk (liftLa γ a - lev g a)) = 0 := by
        rw [hfr, hx]
        funext j
        simp
      have h5 := (AddEquiv.map_eq_zero_iff (fr v)).1 h4
      rw [Submodule.Quotient.mk_eq_zero, htp] at h5
      exact h5
    have h3 := mem_iInf_smul_top (typePrime_coprime (l := l)) hall
    have hle' : ⨅ v, typePrime l v ≤ l.Mb := iInf_typePrime_le.trans
      (sup_le le_rfl ((Ideal.span_singleton_le_iff_mem _).2 (by rw [← hM]; exact natCast_M_mem l)))
    exact Submodule.smul_mono_left hle' h3
  · intro γ hγ
    rw [typeRed_eq_one, mem_grpR_iff]
    intro v q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have h1 : γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (liftLa γ a) := (liftLa_spec γ a).symm
    rw [h1, ← Submodule.Quotient.mk_sub]
    have h2 : liftLa γ a - a ∈ typePrime l₂ v • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
      Submodule.smul_mono_left ((le_sup_left : l.Mb ≤ typePrime l v).trans (htp v).ge) (hγ a)
    exact map_mem_smul_top (l₂.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ h2

end Main

end GlobalTheory.TypeFrameCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryStabilizerTransitionSelfDualFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameChange

open Formalism.L2.DIV
open scoped Matrix TensorProduct

set_option synthInstance.maxHeartbeats 160000

private theorem int_of_parts {R : Type} [CommRing R] (O : Subring R) {n : Type} [Fintype n] [DecidableEq n]
    (G Gi : Matrix n n R) (hGG : G * Gi = 1) (ε ε' : R) (hε : ε ∈ O) (hε' : ε' ∈ O)
    (hs : (ε + ε') • (G - 1) = G - 1) (h1 : ∀ i j, ε * G i j ∈ O) (h2 : ∀ i j, ε' * G i j ∈ O)
    (h3 : ∀ i j, ε * Gi i j ∈ O) (h4 : ∀ i j, ε' * Gi i j ∈ O) :
    (∀ i j, G i j ∈ O) ∧ ∀ i j, Gi i j ∈ O := by
  have hone : ∀ i j, (1 : Matrix n n R) i j ∈ O := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  have hs1 : (1 - ε - ε') ∈ O := O.sub_mem (O.sub_mem O.one_mem hε) hε'
  have hA : (1 - (ε + ε')) • G = (1 - (ε + ε')) • (1 : Matrix n n R) := by
    have : (1 - (ε + ε')) • (G - 1) = 0 := by rw [sub_smul, one_smul, hs, sub_self]
    rw [smul_sub, sub_eq_zero] at this
    exact this
  have hB : (1 - (ε + ε')) • Gi = (1 - (ε + ε')) • (1 : Matrix n n R) := by
    calc (1 - (ε + ε')) • Gi = ((1 - (ε + ε')) • (1 : Matrix n n R)) * Gi := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = ((1 - (ε + ε')) • G) * Gi := by rw [hA]
      _ = (1 - (ε + ε')) • (1 : Matrix n n R) := by rw [Matrix.smul_mul, hGG]
  constructor
  · intro i j
    have e1 := congrFun (congrFun hA i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e1
    have e2 : G i j = (1 - ε - ε') * (1 : Matrix n n R) i j + ε * G i j + ε' * G i j := by
      linear_combination e1
    rw [e2]
    exact O.add_mem (O.add_mem (O.mul_mem hs1 (hone i j)) (h1 i j)) (h2 i j)
  · intro i j
    have e1 := congrFun (congrFun hB i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e1
    have e2 : Gi i j = (1 - ε - ε') * (1 : Matrix n n R) i j + ε * Gi i j + ε' * Gi i j := by
      linear_combination e1
    rw [e2]
    exact O.add_mem (O.add_mem (O.mul_mem hs1 (hone i j)) (h3 i j)) (h4 i j)

private theorem smul_conj {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b b' X : GL n R) (ε : R)
    (h : ε • X.1 = ε • (b' * b⁻¹ : GL n R).1) :
    ε • (b⁻¹ * X * b : GL n R).1 = ε • (b⁻¹ * b' : GL n R).1 ∧
      ε • ((b⁻¹ * X * b)⁻¹ : GL n R).1 = ε • (b'⁻¹ * b : GL n R).1 := by
  have key : ∀ u v : GL n R, ε • (u * X * v : GL n R).1 = ε • (u * (b' * b⁻¹) * v : GL n R).1 := by
    intro u v
    simp only [Units.val_mul] at h ⊢
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · rw [key, show b⁻¹ * (b' * b⁻¹) * b = b⁻¹ * b' by group]
  · have := key (b⁻¹ * X⁻¹) (b * b'⁻¹ * b)
    rw [show b⁻¹ * X⁻¹ * X * (b * b'⁻¹ * b) = b'⁻¹ * b by group,
      show b⁻¹ * X⁻¹ * (b' * b⁻¹) * (b * b'⁻¹ * b) = (b⁻¹ * X * b)⁻¹ by group] at this
    exact this.symm

private theorem smul_conj_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b X : GL n R) (s : R)
    (h : s • (X.1 - 1) = X.1 - 1) :
    s • ((b⁻¹ * X * b : GL n R).1 - 1) = (b⁻¹ * X * b : GL n R).1 - 1 := by
  have e : (b⁻¹ * X * b : GL n R).1 - 1 = (b⁻¹).1 * (X.1 - 1) * b.1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul, Units.val_mul, Units.val_mul]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, h]

private theorem exists_int_GL {R : Type} [CommRing R] (O : Subring R) {n : Type} [Fintype n] [DecidableEq n] (γ : GL n R)
    (h1 : ∀ i j, γ.1 i j ∈ O) (h2 : ∀ i j, (γ⁻¹).1 i j ∈ O) : ∃ y : GL n O, y.1.map O.subtype = γ.1 := by
  let A : Matrix n n O := Matrix.of fun i j => ⟨γ.1 i j, h1 i j⟩
  let B : Matrix n n O := Matrix.of fun i j => ⟨(γ⁻¹).1 i j, h2 i j⟩
  have hA : A.map O.subtype = γ.1 := rfl
  have hB : B.map O.subtype = (γ⁻¹).1 := rfl
  have hinj : Function.Injective (fun M : Matrix n n O => M.map O.subtype) :=
    Matrix.map_injective O.subtype_injective
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, hA⟩
  · show (A * B).map O.subtype = (1 : Matrix n n O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · show (B * A).map O.subtype = (1 : Matrix n n O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem frame_inv_mul_int {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {b b' : GL (Fin n) (EAf D)} (hb : IsFrame b Λ) (hb' : IsFrame b' Λ) (i j : Fin n) :
    (b⁻¹ * b' : GL (Fin n) (EAf D)).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h1 : b'.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [hb']
    intro k
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have h2 := (hb _).1 h1 i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
  exact h2

set_option maxHeartbeats 800000 in

private theorem mem_St_of_comp {D : D7} (e : AE D) (he : e * e = e) (V : HSp D)
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : IsSelfDualC V Λ)
    (b b' : GL (Fin V.rank) (EAf D)) (hb : IsFrame b Λ) (hb' : IsFrame b' Λ) (k : GA D V) (hk : SuppAt e V k)
    (hc : ∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) :
    Formalism.IndefR.Lev.finE V k ∈ St b := by
  have hidem : ∀ a : AE D, a * a = a → toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun a ha =>
    Formalism.IndefR.Fin.LevelGroupLemmas.toEAf_mem_intAf (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, ha]))
  have hε := hidem e he
  have hε' := hidem (cA D e) (by rw [← map_mul, he])
  obtain ⟨X, hX⟩ : ∃ X : GL (Fin V.rank) (EAf D), X = Formalism.IndefR.Lev.finE V k := ⟨_, rfl⟩
  have hXv : X.1 = (mt V k).map (toEAf D) := by rw [hX]; rfl
  have hc' : toEAf D e • X.1 = toEAf D e • (b' * b⁻¹ : GL (Fin V.rank) (EAf D)).1 := by
    rw [hX]; exact Matrix.ext fun i j => hc i j
  obtain ⟨c1, c2⟩ := smul_conj b b' X (toEAf D e) hc'
  have hs : (toEAf D e + toEAf D (cA D e)) • (X.1 - 1) = X.1 - 1 := by
    refine Matrix.ext fun i j => ?_
    have h0 := congrArg (toEAf D) (hk i j)
    have h1 : toEAf D ((mt V k - 1) i j) = (X.1 - 1) i j := by
      rw [hXv, Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]
    rw [map_mul, RingHom.map_add, h1] at h0
    exact h0
  have i1 : ∀ i j, (toEAf D e • (b⁻¹ * X * b : GL (Fin V.rank) (EAf D)).1) i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j; rw [c1]; exact Subring.mul_mem _ hε (frame_inv_mul_int hb hb' i j)
  have i2 : ∀ i j, (toEAf D e • ((b⁻¹ * X * b)⁻¹ : GL (Fin V.rank) (EAf D)).1) i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j; rw [c2]; exact Subring.mul_mem _ hε (frame_inv_mul_int hb' hb i j)
  obtain ⟨j1, j2⟩ := GlobalTheory.ConjIntegral.conj_smul_isIntM V Λ b hΛ hb X (hX ▸ GlobalTheory.LevSplit.finE_mem_UA V k)
    (b⁻¹ * X * b) rfl e i1 i2
  obtain ⟨g1, g2⟩ := int_of_parts (Formalism.L2.Herm.intAf D.host.F D.host.E) _ _ (Units.mul_inv (b⁻¹ * X * b)) _ _ hε hε'
    (smul_conj_sub_one b X _ hs) i1 j1 i2 j2
  obtain ⟨y, hy⟩ := exists_int_GL _ _ g1 g2
  refine ⟨y, ?_⟩
  have hy' : intGL D.host.F D.host.E V.rank y = b⁻¹ * X * b := Units.ext hy
  rw [← hX]
  show b * intGL D.host.F D.host.E V.rank y * b⁻¹ = X
  rw [hy']; group

set_option maxHeartbeats 800000 in

private theorem exists_unitary_frame_change : ∀ {D : D7} (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (b b' : GL (Fin V.rank) (EAf D)), Formalism.L2.DIV.IsFrame b Λ → Formalism.L2.DIV.IsFrame b' Λ →
    ∃ k : GA D V, SuppAt e V k ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ k ∧
      (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) ∧
      ∀ y : (AE D)ˣ, IsDetAt e V k y → Formalism.L2.Pj.FinUnit y := by
  intro D e S hS V Λ hΛ b b' hb hb'
  have he : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hS
  have he' : e * cA D e = 0 := hS.2
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  let inv : EAf D →+* (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)).toRingEquiv.toRingHom
  have hinv : ∀ x, Lev.swapAE D (inv x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a c => rfl
    | add a c ha hc => rw [RingHom.map_add, RingHom.map_add, ha, hc]
  let P : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (b' * b⁻¹ : GL (Fin V.rank) (EAf D)).1
  let Q : Matrix (Fin V.rank) (Fin V.rank) (EAf D) := (b * b'⁻¹ : GL (Fin V.rank) (EAf D)).1
  have hPQ : P * Q = 1 := by
    show (b' * b⁻¹ * (b * b'⁻¹) : GL (Fin V.rank) (EAf D)).1 = 1
    rw [show b' * b⁻¹ * (b * b'⁻¹) = 1 by group]
    rfl
  obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.SplitLift.exists_unitary_prod (infPart D) (finPart D) φ hφ' (cA D)
    GlobalTheory.DualPairCheck.cA_cA _ _ hJ hJK e he he' hinf (P.map inv) (Q.map inv)
    (by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)])
  let k : GA D V := ⟨g, hg⟩
  have hval : ∀ i j, (Lev.finE V k).1 i j = Lev.swapAE D (finPart D (g.1 i j)) := fun i j => rfl
  have hcomp : ∀ i j, toEAf D e * (Lev.finE V k).1 i j = toEAf D e * P i j := by
    intro i j
    have h3 : finPart D e * finPart D (g.1 i j) = finPart D e * inv (P i j) := congrFun (congrFun h2 i) j
    rw [hval, show toEAf D e = Lev.swapAE D (finPart D e) from rfl, ← map_mul, h3, map_mul, hinv]
  have hk : SuppAt e V k := h1
  have hSt := mem_St_of_comp e he V Λ hΛ b b' hb hb' k hk hcomp
  refine ⟨k, hk, GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.stabLat_of_mem_St V Λ b hb k hSt, hcomp, ?_⟩
  intro y hy
  have hyv : (y : AE D) = e * (mt V k).det + (1 - e) := hy
  have hyd : y = Formalism.IndefR.Fin.LevelGroupLemmas.detAt e V k :=
    Units.ext (hyv.trans (Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he V k).symm)
  have hint : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])
  refine ⟨?_, ?_, ?_⟩
  · rw [hyv, RingHom.map_add, map_mul, RingHom.map_sub, map_one, hinf, zero_mul, zero_add, sub_zero]
  · rw [hyd]; exact Formalism.IndefR.Fin.LevelGroupLemmas.finPart_detAt_int he hint V hSt
  · rw [hyd]; exact Formalism.IndefR.Fin.LevelGroupLemmas.finPart_detAt_inv_int he hint V hSt

end GlobalTheory.FrameChange

end

theorem _root_.GlobalTheory.T.exists_unitaryStabilizer_transition_selfDualFrames : ∀ {D : D7} (e : AE D) (S : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e S →
    ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (b b' : GL (Fin V.rank) (EAf D)), Formalism.L2.DIV.IsFrame b Λ → Formalism.L2.DIV.IsFrame b' Λ →
    ∃ k : GA D V, SuppAt e V k ∧ GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ k ∧
      (∀ i j, toEAf D e * (Formalism.IndefR.Lev.finE V k).1 i j = toEAf D e * (b' * b⁻¹).1 i j) ∧
      ∀ y : (AE D)ˣ, IsDetAt e V k y → Formalism.L2.Pj.FinUnit y :=
  GlobalTheory.FrameChange.exists_unitary_frame_change
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypesSeparatedByInertPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_types_separated_by_inert_places : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ((∃ tr, R.TrISem F tr ∧ ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X, (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) → ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2)) → R.TrISem F A3.trI ∧ A3.fam3.TrISep) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → A3.fam3.TypesSep3 := by
  first | exact @GlobalTheory.Hk3.typesSep3_of_pin | exact GlobalTheory.Hk3.typesSep3_of_pin | (intros; apply GlobalTheory.Hk3.typesSep3_of_pin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineWeightCharacterTriangularFrameChangeStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatLineWeight_character_triangular_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (S : Type) [Field S] (t : Ix Dw → Sˣ), (((∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i : Sˣ)) : S) * ∏ i : Fin (Dw.mult τ.1), (t (some ⟨τ.1, i⟩) : S) = ∏ j : Fin (Dw.mult (conjEmb τ.1)), (t (some ⟨conjEmb τ.1, j⟩) : S) := by
  first | exact @GlobalTheory.FlatChar.flatWt_char | exact GlobalTheory.FlatChar.flatWt_char | (intros; apply GlobalTheory.FlatChar.flatWt_char <;> assumption)
end

