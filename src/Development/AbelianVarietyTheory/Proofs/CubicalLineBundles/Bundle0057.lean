import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0024
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0012
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0038
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmActionPolarisedCurveAdjointConj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CurveAdjoint

theorem linear_eq_of_ex {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, u.ex (F z) = u.ex (G z)) : F = G := by
  have hD : ∀ z, (F - G) z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h1 := u.ex_add (G z) ((F - G) z)
    have e : G z + (F - G) z = F z := by simp
    rw [e, h z] at h1
    exact mul_left_cancel (a := u.ex (G z)) (by rw [_root_.mul_one]; exact h1.symm)
  refine LinearMap.ext fun z => ?_
  have hc : Continuous (fun t : ℝ => (⟨(F - G) ((t : ℂ) • z), hD _⟩ : u.Λ)) :=
    Continuous.subtype_mk ((F - G).continuous_of_finiteDimensional.comp
      (Complex.continuous_ofReal.smul continuous_const)) _
  haveI := u.discrete
  have h2 := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := 1) (y := 0))
  simp only [Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul, map_zero] at h2
  exact sub_eq_zero.mp h2

theorem exists_scalar {g : ℕ} (hg : g = 1) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : ∃ c : ℂ, ∀ z, F z = c • z := by
  subst hg
  refine ⟨F (fun _ => 1) 0, fun z => ?_⟩
  have hz : z = z 0 • (fun _ : Fin 1 => (1 : ℂ)) := by
    funext i
    rw [Subsingleton.elim i 0]
    simp
  rw [hz, map_smul]
  funext i
  rw [Subsingleton.elim i 0]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem map_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (j : OK H →+* ℂ) (x y : OK H)
    (h : (y : 𝓞 E) = H.bar x) : j y = starRingEnd ℂ (j x) := by
  obtain ⟨-, huniq, ⟨br, hbr, hw, -⟩, hquad, -⟩ := OK_isDedekindDomain_and_projective E H
  have hy : y = br x := Subtype.ext (h.trans (hbr x).symm)
  have hbw : br (wK H) = 1 - wK H := eq_sub_of_add_eq' hw
  obtain ⟨⟨m₁, m₂⟩, hx, -⟩ := huniq x
  have hN : (1 : ℝ) ≤ (((1 + H.d) / 4 : ℕ) : ℝ) := by
    have := H.d_mod
    exact_mod_cast (by omega : 1 ≤ (1 + H.d) / 4)
  have hq := congrArg j hquad
  simp only [map_add, map_pow, map_natCast] at hq
  have hz : starRingEnd ℂ (j (wK H)) = 1 - j (wK H) := by
    have e := congrArg Complex.re hq
    have f := congrArg Complex.im hq
    simp [pow_two] at e f
    have ha : (j (wK H)).re = 1 / 2 := by
      rcases eq_or_ne (j (wK H)).im 0 with h0 | h0
      · exfalso
        rw [h0] at e
        nlinarith [sq_nonneg ((j (wK H)).re - 1 / 2)]
      · have h2 : 2 * (j (wK H)).re = 1 := by
          apply mul_left_cancel₀ h0
          linear_combination f
        linarith
    apply Complex.ext <;> simp <;> linarith
  rw [hy, hx]
  simp only [map_add, map_mul, map_intCast, hbw, map_sub, map_one, hz]

theorem lamEq_act_bar : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (σ : R →+* ℂ) (P : Out.PolAV (Sp R)) (a : OAct (OK H) P.A), Function.Injective σ → P.g = 1 → ∀ x y : OK H, (y : 𝓞 E) = H.bar x → LamEq P.L (a.act x) (𝟙 P.A) P.L (𝟙 P.A) (a.act y) := by
  intro hT hL E _ _ _ H R _ _ σ P a hσ hg x y hxy
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨Q, φ, hQg, hφ, hLφ⟩ := GlobalTheory.exists_isPolFibre hL.polBaseChange σ P
  haveI : IsCommMonObj Q.A := Q.isAb.comm
  have hQ1 : Q.g = 1 := hQg.trans hg
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, hend, -⟩ := hT Q rig hrig
  have hex : ∀ r : OK H, ∃ c : ℂ, ∃ w' : Q.A ⟶ Q.A, IsMonHom w' ∧ w'.left ≫ φ = φ ≫ (a.act r).left ∧
      ∀ z, u.ex (c • z) = u.ex z ≫ w' := by
    intro r
    haveI := a.hom r
    obtain ⟨w', hw'm, hw'⟩ := GlobalTheory.PairingFibre.exists_hom hφ hφ (a.act r)
    obtain ⟨F, hF⟩ := hend w' hw'm
    obtain ⟨c', hc'⟩ := exists_scalar hQ1 F
    exact ⟨c', w', hw'm, hw', fun z => by rw [← hc' z, hF z]⟩
  choose c w hmon hcomm hlift using hex
  have hcomm' : ∀ r {Z : Scheme.{0}} (h : P.A.left ⟶ Z), (w r).left ≫ φ ≫ h = φ ≫ (a.act r).left ≫ h := by
    intro r Z h
    rw [← Category.assoc, hcomm r, Category.assoc]
  have huniq : ∀ r (c' : ℂ) (w' : Q.A ⟶ Q.A), w'.left ≫ φ = φ ≫ (a.act r).left →
      (∀ z, u.ex (c' • z) = u.ex z ≫ w') → c' = c r := by
    intro r c' w' hw' hl
    have hww : w' = w r := by
      apply Over.OverMorphism.ext
      apply hφ.1.hom_ext
      · rw [hw', hcomm r]
      · rw [Over.w w', Over.w (w r)]
    subst hww
    have he := linear_eq_of_ex u (c' • LinearMap.id) (c r • LinearMap.id) (fun z => by
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [hl, hlift r])
    have he' := congrFun (LinearMap.congr_fun he (fun _ => 1)) ⟨0, by omega⟩
    simpa using he'
  have hone : c 1 = 1 :=
    (huniq 1 1 (𝟙 Q.A) (by rw [a.one]; simp) (fun z => by simp)).symm
  have hmul : ∀ r s, c (r * s) = c r * c s := by
    intro r s
    refine (huniq (r * s) (c r * c s) (w r ≫ w s) ?_ ?_).symm
    · simp only [a.mul, Over.comp_left, Category.assoc, hcomm, hcomm']
    · intro z
      rw [← Category.assoc, ← hlift r z, ← hlift s (c r • z), smul_smul, _root_.mul_comm]
  have hadd : ∀ r s, c (r + s) = c r + c s := by
    intro r s
    refine (huniq (r + s) (c r + c s) (w r * w s) ?_ ?_).symm
    · let jm : Over.mk (Q.A.hom ≫ spMap σ) ⟶ P.A := Over.homMk φ hφ.1.w
      have h := hφ.2 Q.A (w r) (w s) (jm ≫ a.act r) (jm ≫ a.act s) (by simp [jm, hcomm r]) (by simp [jm, hcomm s])
      rw [← h, ← MonObj.comp_mul, ← a.add, Over.comp_left]
      simp [jm]
    · intro z
      rw [add_smul, u.ex_add, hlift r, hlift s, MonObj.comp_mul]
  let j : OK H →+* ℂ := RingHom.mk' ⟨⟨c, hone⟩, hmul⟩ hadd
  have hj : c y = starRingEnd ℂ (c x) := map_bar H j x y hxy
  have hQ : WeilEq Q.L (w x) (𝟙 Q.A) Q.L (𝟙 Q.A) (w y) (𝟙 (Sp ℂ)) := by
    rw [GlobalTheory.T.weilEq_iff_hermForm_eq_complex hT hL Q Q Q Q u u u u Hm Hm χ χ hAH hAH (w x) (𝟙 Q.A) (𝟙 Q.A) (w y)
      (c x • LinearMap.id) LinearMap.id LinearMap.id (c y • LinearMap.id)
      (fun z => by simpa using hlift x z) (fun z => by simp) (fun z => by simp) (fun z => by simpa using hlift y z)]
    intro z v
    simp [hermForm, hj, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, star_smul]
  have hP : WeilEq P.L (a.act x) (𝟙 P.A) P.L (𝟙 P.A) (a.act y) (spMap σ) := by
    have hb := (GlobalTheory.PairingFibre.weilEq_iff hφ hφ hφ hφ P.isLB P.isLB Q.isLB Q.isLB (LBIso.symm hLφ) (LBIso.symm hLφ)
      (f₁ := a.act x) (f₂ := 𝟙 P.A) (g₁ := 𝟙 P.A) (g₂ := a.act y)
      (f₁' := w x) (f₂' := 𝟙 Q.A) (g₁' := 𝟙 Q.A) (g₂' := w y)
      (hcomm x) (by simp) (by simp) (hcomm y) (𝟙 (Sp ℂ))).mp hQ
    rwa [Category.id_comp] at hb
  exact (GlobalTheory.PairingFibre.lamEq_weilEq_over_ring hL R P P P P (a.act x) (𝟙 P.A) (𝟙 P.A) (a.act y)
    (a.hom x) inferInstance inferInstance (a.hom y) ℂ σ).2 inferInstance hσ hP

end GlobalTheory.CurveAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring : Out.Laws → ∀ (R : Type) [CommRing R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (β : R →+* k),
  (LamEq A.L f₁ f₂ B.L g₁ g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β)) ∧ (IsDedekindDomain R → Function.Injective β → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β) → LamEq A.L f₁ f₂ B.L g₁ g₂) := by
  first | exact @GlobalTheory.PairingFibre.lamEq_weilEq_over_ring | exact GlobalTheory.PairingFibre.lamEq_weilEq_over_ring | (intros; apply GlobalTheory.PairingFibre.lamEq_weilEq_over_ring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfPowQuotient
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.PowQuotient

variable {S S' : Scheme.{0}}

theorem isMonHom_prod {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj H] {n : ℕ} (a : Fin n → (G ⟶ H))
    (ha : ∀ i, IsMonHom (a i)) : IsMonHom (∏ i, a i) :=
  Finset.prod_induction a (fun z => IsMonHom z) (fun x y _ _ => isMonHom_mul x y) isMonHom_one fun i _ => ha i

theorem comp_prod {T G H : Over S} [GrpObj H] [IsCommMonObj H] {n : ℕ} (x : T ⟶ G) (a : Fin n → (G ⟶ H)) :
    x ≫ ∏ i, a i = ∏ i, x ≫ a i :=
  map_prod (preHom (G := H) x) a Finset.univ

def incl {G' G : Over S} [GrpObj G'] [GrpObj G] {n : ℕ} (p : Out.IsPowGrp G' G n) (i : Fin n) : G ⟶ G' :=
  powLift p fun k => if k = i then 𝟙 G else 1

end GlobalTheory.PowQuotient

namespace GlobalTheory

open PowQuotient

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieEigenbasisGenericFibreCmTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_eigenbasis_fibre : Out.SecTwistSt → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (K : Type) [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))) (oa : T.pol.OAct (𝓞 E)) (S : Set (E →+* ℂ)) (lab : (E →+* ℂ) → (E →+* K)) (ρ : 𝓞 K), oa.act = T.t.act.act → Function.Bijective lab → ρ ^ 2 = -(H.d : 𝓞 K) → (∀ t, t ∈ S ↔ lab t (H.rt : E) = (ρ : K)) → HasType H T.t.act ρ 1 0 → ∃ (x : KeyIn K) (φ : x.P.A.left ⟶ T.pol.A.left) (τ : Fin x.P.g ≃ S), IsFibreOf T.pol x (gmap K) φ ∧ x.P.g = Module.finrank ℚ E / 2 ∧ IsLieType T.pol oa x φ τ lab := by
  intro hT hL E _ _ _ _ H K _ _ T oa S lab ρ hoa hlab hρ hS hty
  classical
  obtain ⟨-, -, h3⟩ := GlobalTheory.CM.splits_basic E
  obtain ⟨hs1, hs2, -⟩ := h3 K
  have hsp : Splits E K := hs1.2 (by
    rw [← Nat.card_eq_of_bijective lab hlab, Nat.card_eq_fintype_card, NumberField.Embeddings.card])
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  obtain ⟨F₀⟩ := GlobalTheory.CM.GenFib.nonempty_of_baseChange hL.polBaseChange K T.pol
  have hg : T.g = Module.finrank ℚ E / 2 := by
    simpa using (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ T F₀ 1 0 hsp hty hρ).2.2.2.1
  obtain ⟨y, ψ, w, hyg, hψ, hw⟩ := GlobalTheory.KeyPow.exists_keyIn_pullback hT (algebraMap (𝓞 K) K) T.pol (hpos.trans_eq hg.symm)
  have hfib : IsFibreOf T.pol y (spMap (algebraMap (𝓞 K) K)) ψ := ⟨hψ, w, (isGen_iff _).2 hw⟩
  let F : GenFib T.pol := ⟨y.P, ψ, (isFibreOf_iff_isPolFibre _ _ _ _ _ _).1 hfib, y.v, y.basis⟩
  obtain ⟨hrk, hind, -, -, hcard, -⟩ := GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ T F 1 0 hsp hty hρ
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K T.pol F (𝓞 E) T.t.act
  let res : S → (𝓞 E →+* 𝓞 K) := fun t => RingOfIntegers.mapRingHom (lab t)
  have hres : ∀ t (a : 𝓞 E), ((res t a : 𝓞 K) : K) = lab t (a : E) := fun t a => rfl
  have hinj : Function.Injective res := fun s t h => Subtype.ext (hlab.1
    ((hs2 (res t)).unique (fun a => by rw [← h, hres]) (fun a => by rw [hres])))
  have hrt : ∀ t, res t H.rt = ρ := fun t => RingOfIntegers.ext ((hres t _).trans ((hS t).1 t.2))
  have hcS : Nat.card S = Module.finrank ℚ E / 2 := by
    rw [← hcard]
    refine Nat.card_eq_of_bijective (fun t => ⟨res t, hrt t⟩) ⟨fun s t h => hinj (congrArg Subtype.val h), fun τ => ?_⟩
    obtain ⟨τ', hτ', -⟩ := hs2 τ.1
    obtain ⟨t, rfl⟩ := hlab.2 τ'
    refine ⟨⟨t, (hS t).2 (by rw [hτ', τ.2])⟩, Subtype.ext (RingHom.ext fun a => RingOfIntegers.ext ?_)⟩
    exact (hres _ _).trans (hτ' a)
  have hb : ∀ t : S, ∃ b ∈ Submodule.span K (F.eigLat T.t.act (res t) : Set (Fin F.P₀.g → K)), b ≠ 0 := fun t => by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro h
    have := hrk (res t)
    rw [latRank, h, if_pos (hrt t), finrank_bot] at this
    exact zero_ne_one this
  choose b hb hb0 using hb
  have hli : LinearIndependent K b := (hind.comp hinj).linearIndependent _ hb hb0
  have hyg' : y.P.g = Module.finrank ℚ E / 2 := hyg.trans hg
  let e : Fin y.P.g ≃ S := (Finite.equivFinOfCardEq (hcS.trans hyg'.symm)).symm
  let M : Matrix (Fin y.P.g) (Fin y.P.g) K := fun i => b (e i)
  have hM : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.linearIndependent_rows_iff_isUnit.1 (hli.comp e e.injective))
  have := y.P.isAb.comm
  obtain ⟨hex, htan, hcomp, -, hbas⟩ := LieComb.lieComb_algebra K y.P.A _ y.v y.basis.1
  choose v' hv' _ using fun i => hex (M i)
  have hv'b : IsLieBasis v' := (hbas M v' y.basis hv').2 hM
  refine ⟨⟨y.P, y.g_pos, y.rig, y.rig_gen, y.th, y.th_ne, v', hv'b⟩, ψ, e, hfib, hyg', fun a i => ?_⟩
  obtain ⟨-, f₀, -, hf₀, hd⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K T.pol F T.pol F (T.t.act.act a) (T.t.act.hom a)
  have h1 : IsLieComb (r a (M i)) y.v (v' i ≫ f₀) := hd _ (hr a) _ _ (hv' i)
  obtain ⟨w', hw', -⟩ := (LieComb.lieComb_algebra K y.P.A _ v' hv'b.1).1 (Pi.single i (lab (e i) (a : E)))
  have h2 := hcomp _ M v' _ w' hv' hw'
  have h3 : r a (M i) = ∑ j, (Pi.single i (lab (e i) (a : E)) : Fin y.P.g → K) j • M j := by
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp), Pi.single_eq_same]
    exact ((hr' (res (e i)) _).2.1 (hb (e i)) a).trans rfl
  rw [h3] at h1
  refine ⟨w', hw', ?_⟩
  rw [← (hex _).unique h1 h2, hoa]
  exact (congrArg ((v' i).left ≫ ·) hf₀.symm).trans (Category.assoc _ _ _).symm

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InjectiveOfSumEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Indep

section Linear

variable {K V J : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype J]

theorem finrank_le_sum {N : J → Submodule K V} (h : ⨆ i, N i = ⊤) :
    Module.finrank K V ≤ ∑ i, Module.finrank K (N i) := by
  classical
  have hs : Function.Surjective (DirectSum.coeLinearMap N) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, h]
  rw [← Module.finrank_directSum]
  exact LinearMap.finrank_le_finrank_of_surjective hs

theorem iSupIndep_of_sum_le {N : J → Submodule K V} (h : ⨆ i, N i = ⊤)
    (hd : ∑ i, Module.finrank K (N i) ≤ Module.finrank K V) : iSupIndep N := by
  classical
  have hs : Function.Surjective (DirectSum.coeLinearMap N) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, h]
  have he : Module.finrank K (DirectSum J fun i => N i) = Module.finrank K V := by
    rw [Module.finrank_directSum]
    exact le_antisymm hd (finrank_le_sum h)
  exact DirectSum.IsInternal.submodule_iSupIndep
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).2 hs, hs⟩

theorem sum_finrank_eq {N : J → Submodule K V} (hi : iSupIndep N) (h : ⨆ i, N i = ⊤) :
    ∑ i, Module.finrank K (N i) = Module.finrank K V := by
  classical
  rw [← Module.finrank_directSum]
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap N)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi h)).finrank_eq

theorem injective_of_sum_eq {W : J → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (W i)] {M : ∀ i, W i →ₗ[K] V} (h : ⨆ i, LinearMap.range (M i) = ⊤)
    (hd : ∑ i, Module.finrank K (W i) = Module.finrank K V) (j : J) : Function.Injective (M j) := by
  have hle : ∀ i ∈ (Finset.univ : Finset J), Module.finrank K (LinearMap.range (M i)) ≤ Module.finrank K (W i) :=
    fun i _ => LinearMap.finrank_range_le _
  have he := (Finset.sum_eq_sum_iff_of_le hle).1
    (le_antisymm (Finset.sum_le_sum hle) (hd ▸ finrank_le_sum h)) j (Finset.mem_univ _)
  have := LinearMap.finrank_range_add_finrank_ker (M j)
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega

end Linear

open IntCoord in

theorem map_eigLat_le {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} {f : P.A ⟶ P'.A}
    (hf : ∀ x, a.act x ≫ f = f ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : F.IsDiffOf F' f M) (τ : O →+* 𝓞 K) :
    (F.eigLat a τ).map (M.restrictScalars (𝓞 K)) ≤ F'.eigLat a' τ := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨u, hu, he⟩ := ((integral_tangent_coordinates K P F).2.2.2.2.2 O a τ c).1 hc
  refine Submodule.subset_span ⟨u ≫ f, hM u c hu, fun x => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (he x),
    Category.assoc]

theorem letters_independent : ThetaUnifAV → Out.Laws → IndSt := by
  intro hU hL E _ _ _ H K _ _ ρ σ₁ p q X FA FB M hM N
  classical
  haveI : Finite (𝓞 E →+* 𝓞 K) := (Nat.card_pos_iff.1 (X.split ▸ Module.finrank_pos)).2
  haveI := Fintype.ofFinite (𝓞 E →+* 𝓞 K)
  have hρ : ρ ≠ 0 := fun h => by
    have := X.ρ_sq
    rw [h] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hsq : ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = -ρ ↔ ¬ τ H.rt = ρ := fun τ => by
    have e : τ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, X.ρ_sq]; simp
    refine ⟨fun h h' => hρ ?_, fun h => (sq_eq_sq_iff_eq_or_eq_neg.1 e).resolve_left h⟩
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination h - h'
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  have hA : ∀ b : Bool, (∀ τ : 𝓞 E →+* 𝓞 K, latRank K ((FA b).eigLat (X.A b).t.act τ) =
        if τ H.rt = (if b then ρ else -ρ) then 1 else 0) ∧
      iSupIndep (fun τ : 𝓞 E →+* 𝓞 K =>
        Submodule.span K ((FA b).eigLat (X.A b).t.act τ : Set (Fin (FA b).P₀.g → K))) ∧
      ⨆ τ : 𝓞 E →+* 𝓞 K, Submodule.span K ((FA b).eigLat (X.A b).t.act τ : Set (Fin (FA b).P₀.g → K)) = ⊤ ∧
      (FA b).P₀.g = Module.finrank ℚ E / 2 := by
    rintro (_ | _)
    · obtain ⟨a, b, c, d, -⟩ := GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A false) (FA false) 0 1 X.split X.typeM X.ρ_sq
      refine ⟨fun τ => ?_, b, c, by rw [(FA false).fib.1]; simpa using d⟩
      rw [a]
      by_cases h : τ H.rt = ρ
      · rw [if_pos h, if_neg (by simpa [hsq] using h)]
      · rw [if_neg h, if_pos (by simpa [hsq] using h)]
    · obtain ⟨a, b, c, d, -⟩ := GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A true) (FA true) 1 0 X.split X.typeP X.ρ_sq
      refine ⟨fun τ => ?_, b, c, by rw [(FA true).fib.1]; simpa using d⟩
      rw [a]
      simp
  have hB : FB.P₀.g = Module.finrank ℚ E / 2 * (p + q) := by
    rw [FB.fib.1]
    exact (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ X.B FB p q X.split X.typeB X.ρ_sq).2.2.2.1
  have hsur : ⨆ j, LinearMap.range (M j) = ⊤ :=
    GlobalTheory.T.iSup_range_differential_eq_top_of_jointly_onto hU hL K X.B.pol FB σ₁ (Fin p ⊕ Fin q) (fun j => (X.A j.isLeft).pol) (fun j => FA j.isLeft) X.φ M
      inferInstance (fun j => (X.lin j).1) hM fun y => by
        obtain ⟨x, hx⟩ := X.onto y
        exact ⟨p + q, finSumFinEquiv.symm, fun m => x _, hx⟩
  have hdim : ∑ j : Fin p ⊕ Fin q, Module.finrank K (Fin (FA j.isLeft).P₀.g → K) =
      Module.finrank K (Fin FB.P₀.g → K) := by
    simp [(hA _).2.2.2, hB, mul_comm]
  have hinj := injective_of_sum_eq hsur hdim
  have hspan : ∀ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) =
      (Submodule.span K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2 : Set _)).map (M x.1) := fun x => by
    rw [Submodule.map_span]
    rfl
  have hrk : ∀ x, latRank K (N x) = latRank K ((FA x.1.isLeft).eigLat (X.A x.1.isLeft).t.act x.2) := fun x => by
    rw [latRank, hspan]
    exact (Submodule.equivMapOfInjective _ (hinj x.1) _).finrank_eq.symm
  have htop : ⨆ x, Submodule.span K (N x : Set (Fin FB.P₀.g → K)) = ⊤ := by
    rw [iSup_prod, ← hsur]
    refine iSup_congr fun j => ?_
    rw [← Submodule.map_top, ← (hA j.isLeft).2.2.1, Submodule.map_iSup]
    exact iSup_congr fun τ => hspan (j, τ)
  refine ⟨fun x => map_eigLat_le (X.lin x.1).2 (hM x.1) x.2, fun x => ?_, hinj, iSupIndep_of_sum_le htop ?_, htop⟩
  · rw [hrk, (hA _).1]
  · rw [← hdim, Fintype.sum_prod_type]
    refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
    rw [← sum_finrank_eq (hA j.isLeft).2.1 (hA j.isLeft).2.2.1]
    exact Finset.sum_congr rfl fun τ _ => hrk (j, τ)

end GlobalTheory.CM.Indep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIsogenousDedekind
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.AmpleDedekind

theorem range_spMap_fractionRing (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Set.range (spMap (algebraMap R K)) = {genericPoint (Sp R)} := by
  have h : ∀ p : Sp K, spMap (algebraMap R K) p = genericPoint (Sp R) := fun p => by
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap R K) (PrimeSpectrum.asIdeal p) = ⊥
    have hp : PrimeSpectrum.asIdeal p = ⊥ := Ideal.eq_bot_of_prime (K := K) _ (h := p.isPrime)
    rw [hp]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  exact Set.eq_singleton_iff_unique_mem.2
    ⟨⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), h _⟩, by rintro _ ⟨p, rfl⟩; exact h p⟩

theorem relAmple_of_generic_of_isogenous : Out.Laws → Out.Laws2 → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp R)) (B : Over (Sp R)) [GrpObj B] (Ψ : P.A ⟶ B) (M : LB B.left) (B₀ : Over (Sp K)) [GrpObj B₀] (φ : B₀.left ⟶ B.left) (M₀ : LB B₀.left), IsAbelianScheme B → M.IsLB → M₀.IsLB → IsFinite Ψ.left → Flat Ψ.left → Surjective Ψ.left → IsGrpPullback B₀ B (spMap (algebraMap R K)) φ → LBIso M₀ (M.pull φ) → Out.RelAmple B₀ M₀ → Out.RelAmple B M := by
  intro h₁ h₂ R K _ _ _ _ _ P B _ Ψ M B₀ _ φ M₀ hB hM hM₀ hfin hfl hsurj hpb hiso hamp
  have := hB.proper
  have := P.isAb.proper
  have hsq := hpb.1
  have : IsProper B₀.hom := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : IsLocallyNoetherian (Sp R) := inferInstance
  have a₀ : IsAmpleLB (M.pull φ) :=
    (isAmpleLB_congr hM₀ (LB.isLB_pull hM φ) hiso).1 ((relAmple_iff_isAmpleLB_of_isAffine B₀ hM₀).1 hamp)
  let x := spMap (algebraMap R K)
  let g : pullback P.A.hom x ⟶ B₀.left :=
    hsq.lift (pullback.fst P.A.hom x ≫ Ψ.left) (pullback.snd P.A.hom x)
      (by rw [Category.assoc, Over.w Ψ]; exact pullback.condition)
  have e₁ : g ≫ φ = pullback.fst P.A.hom x ≫ Ψ.left := hsq.lift_fst _ _ _
  have e₂ : g ≫ B₀.hom = pullback.snd P.A.hom x := hsq.lift_snd _ _ _
  have sq : IsPullback (pullback.fst P.A.hom x) g Ψ.left φ := by
    refine IsPullback.of_bot ?_ e₁.symm hsq
    rw [e₂, Over.w Ψ]
    exact IsPullback.of_hasPullback _ _
  have : IsFinite g := MorphismProperty.of_isPullback (P := @IsFinite) sq hfin
  have hΨ := LB.isLB_pull hM Ψ.left
  have a₁ : IsAmpleLB ((M.pull Ψ.left).pull (pullback.fst P.A.hom x)) :=
    (isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hM φ) g) (LB.isLB_pull hΨ _)
      (FiniteAmple.lbIso_pull_pull φ hM e₁)).1 (a₀.pull_of_isFinite g)
  have : IsProper ((Over.pullback x).obj P.A).hom :=
    inferInstanceAs (IsProper (pullback.snd P.A.hom x))
  have a₂ : Out.RelAmple P.A (M.pull Ψ.left) :=
    AmpleSpecialisation.relAmple_of_genericFibre h₁ h₂ (Sp R) P (M.pull Ψ.left) K x hΨ (range_spMap_fractionRing R K)
      ((relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback x).obj P.A) (LB.isLB_pull hΨ _)).2 a₁)
  exact (relAmple_finite_pow_iso (Sp R) P.A B Ψ M 1 one_pos P.isAb hB hM hfin).2.2.1 hfl hsurj a₂

end GlobalTheory.AmpleDedekind
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TwoMulDegEigenLatticePolarizedAbelianSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_deg_eigenLattice_polarizedAbelianScheme : DegSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (P : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A), (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → Splits E K → ρ ^ 2 = -(H.d : 𝓞 K) → HasType H act ρ 1 0 → ∀ (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ((2 * deg h (F.eigLat act τ) : ℝ) : ℂ) = logOm E χ := by
  first | exact @GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV | exact GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV | (intros; apply GlobalTheory.LamF.two_mul_deg_eigLat_of_polAV <;> assumption)
end

