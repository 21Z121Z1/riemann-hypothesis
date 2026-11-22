import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0266
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0267

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexCoordinatesColumnFieldIdentification
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TwU.SeamEmb

open Formalism.L2.Ker

theorem tau_nonempty' (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

variable {D : D7} {X : Fields} (s : Seam D X)

theorem iE_single {a : ℕ} (j : Fin a) : (fun k => s.iE ((Pi.single j (1 : X.E) : Sp X.E a) k)) = (Pi.single j 1 : Fin a → D.host.E) := by
  funext k
  by_cases h : k = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem seamHom_injective {a b : ℕ} : Function.Injective (seamHom s (a := a) (b := b)) := by
  intro x x' h
  refine LinearMap.ext fun v => funext fun l => ?_
  have e1 := seamHom_apply s x (fun k => s.iE.symm (v k)) l
  have e2 := seamHom_apply s x' (fun k => s.iE.symm (v k)) l
  simp only [RingEquiv.apply_symm_apply] at e1 e2
  rw [← e1, ← e2, h]

theorem seamHom_surjective {a b : ℕ} : Function.Surjective (seamHom s (a := a) (b := b)) := by
  intro y
  refine ⟨Matrix.toLin' ((LinearMap.toMatrix' y).map s.iE), ?_⟩
  unfold seamHom
  rw [LinearMap.toMatrix'_toLin']
  have : ((LinearMap.toMatrix' y).map s.iE).map s.iE.symm = LinearMap.toMatrix' y := by
    ext p q; simp
  rw [this, Matrix.toLin'_toMatrix']

theorem embH_seamHom (hs : s.Ok) (δ : ℂ) {a b : ℕ} (x : HomE D.host.E a b) :
    embH (X.embC s.σ₀) δ (seamHom s x) = fun τ => embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x (s.iT τ) := by
  funext τ i j
  show δ * X.embC s.σ₀ τ (seamHom s x (Pi.single j 1) i) = δ * TaylorLogMetric.embT D (s.iT τ) (x (Pi.single j 1) i)
  congr 1
  show s.σ₀ (X.emb τ _) = _
  rw [hs.1, seamHom_apply, iE_single]

theorem embH_injective {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι]
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) {a b : ℕ} : Function.Injective (embH emb δ (a := a) (b := b)) := by
  intro x y h
  obtain ⟨τ⟩ := (inferInstance : Nonempty ι)
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring (funext fun i => ?_)
  have := congrFun (congrFun (congrFun h τ) i) j
  simp only [embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  exact (emb τ).injective (mul_left_cancel₀ hδ this)

end GlobalTheory.TwU.SeamEmb

namespace GlobalTheory.TwU.SeamEmb

open Formalism.L2.Ker

theorem seam_coords : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (δ : ℂ) {a b : ℕ}, Function.Bijective (seamHom s (a := a) (b := b)) ∧ (∀ x : HomE D.host.E a b, embH (X.embC s.σ₀) δ (seamHom s x) = fun τ => embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x (s.iT τ)) ∧ (∀ (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ v : VV D.what₂.Tau a b, (fun τ => v (s.iT τ)) ∈ laV (X.embC s.σ₀) δ M ↔ v ∈ laV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ M') ∧ (δ ≠ 0 → ∀ (Ξ : HomE X.E a b → ℂ) (v : VV D.what₂.Tau a b), onV (X.embC s.σ₀) δ Ξ (fun τ => v (s.iT τ)) = onV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ (fun x => Ξ (seamHom s x)) v) := by
  intro D X s hs δ a b
  have hemb := embH_seamHom s hs δ (a := a) (b := b)
  have hcomp : ∀ (x : HomE D.host.E a b) (v : VV D.what₂.Tau a b),
      embH (X.embC s.σ₀) δ (seamHom s x) = (fun τ => v (s.iT τ)) ↔ embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v := by
    intro x v
    rw [hemb]
    constructor
    · intro h
      funext σ
      have := congrFun h (s.iT.symm σ)
      simpa using this
    · intro h; rw [h]
  refine ⟨⟨seamHom_injective s, seamHom_surjective s⟩, hemb, ?_, ?_⟩
  · intro M M' hM v
    constructor
    · rintro ⟨y, hy, hyv⟩
      obtain ⟨x, rfl⟩ := seamHom_surjective s y
      exact ⟨x, (hM x).1 hy, (hcomp x v).1 hyv⟩
    · rintro ⟨x, hx, hxv⟩
      exact ⟨seamHom s x, (hM x).2 hx, (hcomp x v).2 hxv⟩
  · intro hδ Ξ v
    haveI : Nonempty D.what₂.Tau := tau_nonempty' D
    haveI : Nonempty X.Tau := ⟨s.iT.symm (Classical.arbitrary _)⟩
    have hex : (∃ y, embH (X.embC s.σ₀) δ y = fun τ => v (s.iT τ)) ↔ ∃ x, embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v := by
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨x, rfl⟩ := seamHom_surjective s y
        exact ⟨x, (hcomp x v).1 hy⟩
      · rintro ⟨x, hx⟩
        exact ⟨seamHom s x, (hcomp x v).2 hx⟩
    unfold onV
    by_cases h' : ∃ x, embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v
    · have h := hex.2 h'
      rw [dif_pos h, dif_pos h']
      congr 1
      apply embH_injective (X.embC s.σ₀) hδ
      rw [h.choose_spec, (hcomp _ v).2 h'.choose_spec]
    · have h : ¬ ∃ y, embH (X.embC s.σ₀) δ y = fun τ => v (s.iT τ) := fun h => h' (hex.1 h)
      rw [dif_neg h, dif_neg h']

end GlobalTheory.TwU.SeamEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepLocalDatumInvariantCosetMove
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section
namespace GlobalTheory.PsiCosetInv

open GlobalTheory.TopInv

variable {E K : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem core (Psi : Sp E n → K) [Zero K] (q : E) (hq : q ≠ 0) (hqi : IntAt P q) (e e' D : ℕ) (hD : e + e' ≤ D)
    (hInv : ∀ y z : Sp E n, (∀ i, IntAt P ((q ^ e)⁻¹ * z i)) → Psi (y + z) = Psi y)
    (hSupp : ∀ y : Sp E n, Psi y ≠ 0 → ∀ i, IntAt P (q ^ e' * y i))
    (k : Sp E n ≃ₗ[E] Sp E n)
    (hkint : ∀ x : Sp E n, (∀ i, IntAt P (k x i)) → ∀ i, IntAt P (x i))
    (hk : ∀ s l, IntAt P ((q ^ D)⁻¹ * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)))
    (w w₁ : Sp E n) (hc : ∀ l, IntAt P ((q ^ e)⁻¹ * (k.symm w₁ - w) l)) :
    Psi w₁ = Psi w := by
  by_cases hboth : Psi w₁ = 0 ∧ Psi w = 0
  · rw [hboth.1, hboth.2]
  set u := k.symm w₁ with hu
  have hqpow : ∀ m : ℕ, IntAt P (q ^ m) := fun m => mem_intS.1 ((intS P).pow_mem (mem_intS.2 hqi) m)

  have hU : ∀ i, IntAt P (q ^ e' * u i) := by
    by_cases hw : Psi w = 0
    · have hw₁ : Psi w₁ ≠ 0 := fun h => hboth ⟨h, hw⟩
      have h1 := hSupp w₁ hw₁
      have h2 : ∀ i, IntAt P (k (q ^ e' • u) i) := by
        intro i
        rw [map_smul, hu, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
        exact h1 i
      intro i
      have := hkint _ h2 i
      rwa [Pi.smul_apply, smul_eq_mul] at this
    · have h1 := hSupp w hw
      intro i
      have e1 : q ^ e' * u i = q ^ e' * w i + q ^ (e + e') * ((q ^ e)⁻¹ * (u - w) i) := by
        rw [Pi.sub_apply, pow_add]
        field_simp
        ring
      rw [e1]
      exact mem_intS.1 ((intS P).add_mem (mem_intS.2 (h1 i))
        ((intS P).mul_mem (mem_intS.2 (hqpow _)) (mem_intS.2 (hc i))))

  have hz : ∀ l, IntAt P ((q ^ e)⁻¹ * (w₁ - w) l) := by
    intro l
    have hsum : u = ∑ s, u s • (Pi.single s 1 : Sp E n) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hw₁ : w₁ = k u := by rw [hu, LinearEquiv.apply_symm_apply]
    obtain ⟨t, ht⟩ : ∃ t, D = e + e' + t := ⟨D - (e + e'), by omega⟩
    have e2 : (q ^ e)⁻¹ * (w₁ - w) l =
        (∑ s, (q ^ e' * u s) * ((q ^ D)⁻¹ * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)) * q ^ t) +
          (q ^ e)⁻¹ * (u - w) l := by
      have e3 : (w₁ - w) l = (∑ s, u s * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l)) + (u - w) l := by
        have e4 : (k u - u) l = ∑ s, u s * (k (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l) := by
          conv_lhs => rw [hsum]
          rw [map_sum, ← Finset.sum_sub_distrib, Finset.sum_apply]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_smul, ← smul_sub, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
        rw [← e4, hw₁]
        simp only [Pi.sub_apply]
        ring
      rw [e3, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ht, pow_add, pow_add]
      field_simp
    rw [e2]
    refine mem_intS.1 ((intS P).add_mem ((intS P).sum_mem fun s _ => ?_) (mem_intS.2 (hc l)))
    exact (intS P).mul_mem ((intS P).mul_mem (mem_intS.2 (hU s)) (mem_intS.2 (hk s l))) (mem_intS.2 (hqpow t))
  have := hInv w (w₁ - w) hz
  rwa [add_sub_cancel] at this

end GlobalTheory.PsiCosetInv

namespace GlobalTheory.PsiCosetInv

open GlobalTheory.TopInv

theorem psiAt_coset : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    ChIdx.Ok Ch sel mu cst L G m2 → ∀ (al : L.β m2) (P : rowSG Pr sel mu) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (k : GLint X.E (R.N (m2 + 1)) P.1)
    (w w₁ : Sp X.E (R.N (m2 + 1))),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N (m2 + 1))) l))) →
    SameCoset sel mu cst P (k.1.symm w₁) w →
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w₁ = PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w := by
  intro X Pr R Ch sel S mu cst L G m2 hL al P x₀ k w w₁ hk hc
  have hInv := hL.psiInv al P x₀
  have hSupp := hL.psiSupp al P x₀
  unfold SameCoset at hc
  have hkint : ∀ x : Sp X.E (R.N (m2 + 1)), (∀ i, IntAt P.1 (k.1 x i)) → ∀ i, IntAt P.1 (x i) := by
    intro x hx
    have h1 : k.1 x ∈ stdAt X.E (R.N (m2 + 1)) P.1 := (mem_localization_standardLattice P.1 _).2 hx
    exact (mem_localization_standardLattice P.1 _).1 ((k.2 x).1 h1)
  have hq := qOf_ne (E := X.E) P.1
  have hqi : IntAt P.1 ((qOf P.1 : ℕ) : X.E) := intAt_nat (P := P.1) _
  by_cases hP : P.1 ∈ Pr.vGs
  · simp only [if_pos hP] at hInv hSupp hc
    exact core _ _ hq hqi 0 1 (cst.D P) (by rw [hL.depthG P hP]) hInv hSupp k.1 hkint hk w w₁ hc
  · simp only [if_neg hP] at hInv hSupp hc
    exact core _ _ hq hqi cst.M cst.M (cst.D P) (by have := hL.depthQ P hP; omega) hInv hSupp k.1 hkint hk w w₁ hc

end GlobalTheory.PsiCosetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealCharacterClassLatticeEq
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem chi_detId_lat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => (∀ (N : ℕ) (M M' : SDLat D.host.E N), ∀ g ∈ Formalism.L2.Herm.UstdAf D.sp.cm N, Formalism.L2.Herm.Carries g M.1 M'.1 → ∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y g → D.relDet N M M' = QuotientGroup.mk (dtU y)) → (∀ i hi β, latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb = StandardLatticesGL3.stdL D (D.R.N i)) → ∀ i (hi : i ≤ D.R.m) c, t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (t.seam.lat ((t.rd u μ).N i c))) = ((D.chiD ((t.O u μ).dt i c) : ℂˣ) : ℂ)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ _ _ i hi c
  rw [← t.O_lat, t.χ_rec, ← Formalism.L2.Ker.initial_lattice_eq_standard (t.O u μ) i, ← t.idl_ok.2.2.2.2 _ ((t.O u μ).L0 i) ((t.O u μ).lat i c),
    ← (t.O u μ).dt_lat, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
  rfl

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhereStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normOne_idele_order_one_trivial_elsewhere : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime], LocGood σ J A → ∀ v, ∃ π ∈ U1 σ, OneOff (A.pl v).1 π ∧ ordA A v π = 1 := by
  first | exact @GlobalTheory.TwV.Xc.Unif.exists_unif | exact GlobalTheory.TwV.Xc.Unif.exists_unif | (intros; apply GlobalTheory.TwV.Xc.Unif.exists_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOtherSplitPlaceWithDistinctRealPlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

namespace GlobalTheory.OtherSplitPlace

theorem exists_isSplitAt_under_ne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w₀ : HeightOneSpectrum (𝓞 E)), ∃ w₁ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₁ ∧
      w₁.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  intro E _ _ _ w₀
  obtain ⟨p, hp, hmp, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E (Ideal.absNorm w₀.asIdeal)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _

  have hsplit : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → GlobalTheory.UnitaryBC.IsSplitAt w := by
    intro w hw
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
      rwa [map_natCast]
    obtain ⟨a, b, hab, ha, hb⟩ :=
      GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
    by_cases h : a = w
    · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
    · exact ⟨a, h, HeightOneSpectrum.ext ha⟩

  haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := hQ ▸ Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  let w₁ : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩
  refine ⟨w₁, hsplit w₁ hpQ, fun heq => ?_⟩

  have hp₀ : (p : 𝓞 E) ∈ w₀.asIdeal := by
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w₁.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₁.asIdeal
      rw [map_natCast]; exact hpQ
    rw [heq] at hv
    have : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₀.asIdeal := hv
    rwa [map_natCast] at this
  have hN : ((Ideal.absNorm w₀.asIdeal : ℕ) : 𝓞 E) ∈ w₀.asIdeal := Ideal.absNorm_mem _
  have hN0 : 0 < Ideal.absNorm w₀.asIdeal :=
    Nat.pos_of_ne_zero (fun h => w₀.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hcop : Nat.Coprime p (Ideal.absNorm w₀.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => absurd (Nat.le_of_dvd hN0 h) (not_le.mpr hmp))
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 E))
  apply w₀.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using hp₀
  · simpa using hN

end GlobalTheory.OtherSplitPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpan
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwU.MuUnr

theorem le_exp_neg_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  rw [← WithZero.exp_log h0] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem finPart_eq_one {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (z : (GlobalTheory.CMVal.Af E)ˣ)
    (hu : ∀ P, Valued.v ((z : GlobalTheory.CMVal.Af E) P) = 1)
    (hc : ∀ P, χ.UnrAt P ∨ (χ.TameAt P ∧ Valued.v ((z : GlobalTheory.CMVal.Af E) P - 1) < 1)) :
    GlobalTheory.CMVal.finPart χ z = 1 := by
  have e : (fun P => χ.loc P (GlobalTheory.CMVal.coord P z)) = fun _ => 1 := funext fun P => by
    rcases hc P with h | ⟨h, h'⟩
    · exact h _ (hu P)
    · exact h _ (hu P) (le_exp_neg_one' h')
  have h := GlobalTheory.CMVal.Fibre.hasProd_loc χ z
  rw [e] at h
  exact h.unique hasProd_one

theorem exists_pow_eq_span {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (n : ℕ) (s : 𝓞 F), 0 < n ∧ v.asIdeal ^ n = Ideal.span {s} := by
  classical
  have hv : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  set n := Fintype.card (ClassGroup (𝓞 F)) with hn
  have hvn : v.asIdeal ^ n ∈ nonZeroDivisors (Ideal (𝓞 F)) := pow_mem hv n
  have e : (⟨v.asIdeal ^ n, hvn⟩ : nonZeroDivisors (Ideal (𝓞 F))) = ⟨v.asIdeal, hv⟩ ^ n := Subtype.ext (by simp)
  have h1 : ClassGroup.mk0 ⟨v.asIdeal ^ n, hvn⟩ = 1 := by
    rw [e, map_pow]
    exact pow_card_eq_one
  obtain ⟨s, hs⟩ := ((ClassGroup.mk0_eq_one_iff hvn).1 h1).principal
  exact ⟨n, s, Fintype.card_pos, hs⟩

theorem one_sub_eps_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ s : 𝓞 F, s ∈ v.asIdeal ∧ ∃ c ∈ RInt F E,
      1 - Formalism.UG.P.afsplitEps E v = (algebraMap F E (s : F) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * c := by
  obtain ⟨n, s, hn, hs⟩ := exists_pow_eq_span v
  have hsv : s ∈ v.asIdeal := Ideal.pow_le_self hn.ne' (hs ▸ Ideal.mem_span_singleton_self s)
  have hsw : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → s ∉ w.asIdeal := fun w hw h => by
    have h1 : v.asIdeal ^ n ≤ w.asIdeal := by rw [hs, Ideal.span_le, Set.singleton_subset_iff]; exact h
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top (w.isPrime.le_of_pow_le h1))).symm
  have hs0 : (s : F) ≠ 0 := by
    intro h0
    have : s = 0 := by exact_mod_cast h0
    subst this
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hs
    exact v.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hs)
  let a : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (s : F)⁻¹ * (1 - Formalism.UG.P.afsplitI v 1)
  have ha : a ∈ intAd F := by
    intro w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((((s : F)⁻¹ : F) : HeightOneSpectrum.adicCompletion F w) * ((1 : HeightOneSpectrum.adicCompletion F w) - Formalism.UG.P.afsplitI v 1 w)) ≤ 1
    by_cases hw : w = v
    · subst hw
      rw [Formalism.UG.P.afsplitI_self, sub_self, mul_zero, map_zero]
      exact zero_le'
    · rw [Formalism.UG.P.afsplitI_ne v w hw, sub_zero, mul_one, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
        show ((s : F)) = algebraMap (𝓞 F) F s from rfl, (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 (hsw w hw), inv_one]
  refine ⟨s, hsv, (1 : E) ⊗ₜ[F] a, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩), ?_⟩
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    Formalism.UG.P.afsplitEps, show (1 : E ⊗[F] HeightOneSpectrum.adicCompletion F v) = 1 ⊗ₜ[F] 1 from rfl, Formalism.UG.P.afsplitIE_tmul,
    Algebra.TensorProduct.one_def, ← TensorProduct.tmul_sub]
  congr 1
  rw [Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hs0, (algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_one, one_mul]

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU.MuUnr

open GlobalTheory.Mem.Col2 (afIso afIso_tmul_one mem_rInt_iff)

theorem val_afIso_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {x : (AfE F E)ˣ} (hx : x ∈ intU F E) (P : HeightOneSpectrum (𝓞 E)) : Valued.v (afIso F E (x : AfE F E) P) = 1 := by
  obtain ⟨h1, h2⟩ := (Submonoid.mem_units_iff _ x).1 hx
  have a1 := (mem_rInt_iff F E _).1 h1 P
  have a2 := (mem_rInt_iff F E _).1 h2 P
  have e : afIso F E (x : AfE F E) P * afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1 := by
    rw [show afIso F E (x : AfE F E) P * afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E) P =
      (afIso F E (x : AfE F E) * afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E)) P from rfl, ← map_mul, Units.mul_inv, map_one]; rfl
  have e2 := congrArg Valued.v e
  rw [map_mul, map_one] at e2
  exact le_antisymm a1 (by
    by_contra hlt
    push_neg at hlt
    have := mul_le_mul' (le_refl (Valued.v (afIso F E (x : AfE F E) P))) a2
    rw [mul_one, e2] at this
    exact not_le.2 hlt this)

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU.MuUnr

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

theorem host_conj_F (r : 𝓞 D.host.F) :
    D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r)) =
      algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) :=
  (D.host.conjE_mem_hostF_iff _).1 (r : D.host.F).2

theorem isOver_conjP (t : KerEntTied ex) (v : HeightOneSpectrum (𝓞 D.host.F)) (P : HeightOneSpectrum (𝓞 t.X.E))
    (h : IsOver v (seamP t.seam P)) : IsOver v (seamP t.seam (conjPrime₂ P)) := by
  unfold IsOver at h ⊢
  rw [h]
  ext r
  simp only [Ideal.mem_comap]
  set a := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r
  set x := (RingOfIntegers.mapRingEquiv t.seam.iE).symm a
  have hxa : RingOfIntegers.mapRingEquiv t.seam.iE x = a := RingEquiv.apply_symm_apply _ _
  rw [← hxa, mem_seamP, mem_seamP, mem_conjP]
  have hc : cO t.X.E x = x := by
    refine RingOfIntegers.ext (t.seam.iE.injective ?_)
    change t.seam.iE (star (x : t.X.E)) = t.seam.iE (x : t.X.E)
    rw [t.seam_ok.2]
    change D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingEquiv t.seam.iE x)) = _
    rw [hxa, host_conj_F]
    exact (congrArg (algebraMap (𝓞 D.host.E) D.host.E) hxa).symm
  rw [hc]

theorem exists_underSB (t : KerEntTied ex) (μ : D.what₂.Tup) (P : HeightOneSpectrum (𝓞 t.X.E)) (k : Fin 2)
    (hk : ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal) : ∃ v, UnderSB t μ v ∧ IsOver v (seamP t.seam P) := by
  classical
  have hPr := t.pr_ok
  let v : HeightOneSpectrum (𝓞 D.host.F) := (seamP t.seam P).under (𝓞 D.host.F)
  have hv : IsOver v (seamP t.seam P) := rfl
  refine ⟨v, ?_, hv⟩
  have h0 : t.X.conjO (t.Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := t.Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  have hsub : ∀ Q, Q ∈ t.Pr.vG k → Q ∈ SB t μ := fun Q hQ => Finset.mem_union_left _ (by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ])
  rw [← hPr.piG_norm k] at hk
  rcases P.isPrime.mem_or_mem hk with h | h
  · refine ⟨conjPrime₂ P, hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 ?_), isOver_conjP t v P hv⟩
    rw [mem_conjP]
    exact (cO_cO (t.Pr.piG k)).symm ▸ h
  · exact ⟨P, hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 h), hv⟩

end GlobalTheory.TwU.MuUnr

namespace GlobalTheory.TwU

open GlobalTheory.Mem.Col2 (afIso afIso_tmul_one mem_rInt_iff)
open GlobalTheory.TwU.MuUnr

end GlobalTheory.TwU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrimeUnderFirstFactorAtPlaceOverPStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_under_firstFactor_at_placeOverP : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n p : ℕ) [Fact p.Prime] (G : GAtP p) (A : LocAt F E n G), LocInt A → SplAlg A → ∀ v, ∃ P : HeightOneSpectrum (𝓞 E), PrimeOf p (G.P.W v) (A.iw v) P ∧ (∀ (y : G.P.W v) (k : ℕ), ∃ (x : 𝓞 E) (z : G.P.W v), A.iw v x = algebraMap _ _ (y + (p : G.P.W v) ^ k * z)) ∧ ((p : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ ((p : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  first | exact @GlobalTheory.TwV.Xc.PrimeAt.exists_primeOf_place | exact GlobalTheory.TwV.Xc.PrimeAt.exists_primeOf_place | (intros; apply GlobalTheory.TwV.Xc.PrimeAt.exists_primeOf_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldIsoMatrixCongruenceAutomorphismCongruenceStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldIso_matrixCongruence_automorphismCongruence : ∀ {D : D7} {X : Fields} (s : Seam D X) {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ) (g : Sp X.E N ≃ₗ[X.E] Sp X.E N), (∀ a b, IntAt (seamP s P) ((((qOf (seamP s P) : ℕ) : D.host.E) ^ n)⁻¹ * (((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) - 1) a b)) → ∀ s' l, IntAt P (((qOf P : X.E) ^ n)⁻¹ * (g (Pi.single s' (1 : X.E)) l - (Pi.single s' (1 : X.E) : Sp X.E N) l)) := by
  first | exact @GlobalTheory.SeamCong.cong_seam | exact GlobalTheory.SeamCong.cong_seam | (intros; apply GlobalTheory.SeamCong.cong_seam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAtStatement
section
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAt_of_adelic_integralAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) (x : E), IntAtA (F := F) P (iA F E x) → IntAt P x := by
  first | exact @GlobalTheory.RatInt.intAt_of_intAtA | exact GlobalTheory.RatInt.intAt_of_intAtA | (intros; apply GlobalTheory.RatInt.intAt_of_intAtA <;> assumption)
end

