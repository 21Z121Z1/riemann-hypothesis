import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2585
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2608
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitMapSnd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassTorsionPointLocalScheme
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem eq_section_of_isDominant {D G X' V Y₀ Y : Scheme.{0}} [IsReduced D] (g : G ⟶ X') [IsSeparated g]
    (ℓ : V ⟶ X') [IsOpenImmersion ℓ] (σ : D ⟶ G) (s : V ⟶ G) (hs : s ≫ g = ℓ) (y₀ : Y₀ ⟶ D) [IsDominant y₀]
    (z₀ : Y₀ ⟶ V) (h₀ : y₀ ≫ σ = z₀ ≫ s) (y : Y ⟶ D) (z : Y ⟶ V) (h : y ≫ σ ≫ g = z ≫ ℓ) :
    y ≫ σ = z ≫ s := by
  have h₀' : y₀ ≫ σ ≫ g = z₀ ≫ ℓ := by rw [reassoc_of% h₀, hs]
  have : IsReduced (pullback (σ ≫ g) ℓ) := isReduced_of_isOpenImmersion (pullback.fst (σ ≫ g) ℓ)
  have hd : IsDominant (pullback.lift y₀ z₀ h₀') := by
    constructor
    have h1 : Dense (Set.range y₀) := y₀.denseRange
    have h2 := h1.preimage (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.isOpenMap
    refine h2.mono ?_
    rintro u ⟨t, ht⟩
    refine ⟨t, (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.injective ?_⟩
    rw [← ht, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  have key : pullback.fst (σ ≫ g) ℓ ≫ σ = pullback.snd (σ ≫ g) ℓ ≫ s := by
    refine ext_of_isDominant_of_isSeparated (s := g) ?_ (pullback.lift y₀ z₀ h₀') ?_
    · rw [Category.assoc, Category.assoc, hs, pullback.condition]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, h₀]
  have := pullback.lift y z h ≫= key
  rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this

theorem fromSpecStalk_killed {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) [Etale (torsion G n).hom]
    (a : G ⟶ G) [IsMonHom a] (ha : a ≫ mulN G n = mulN G n ≫ a)
    (K : Type) [Field K] (P : Sp K ⟶ (torsion G n).left)
    (hP : P ≫ (torsion.ι G n).left ≫ a.left =
      P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K) :
    (torsion G n).left.fromSpecStalk (P x) ≫ (torsion.ι G n).left ≫ a.left =
      (torsion G n).left.fromSpecStalk (P x) ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hι : torsion.ι G n ≫ mulN G n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))
  have h0 : (MonObj.one : 𝟙_ (Over X') ⟶ G) ≫ mulN G n = (MonObj.one : 𝟙_ (Over X') ⟶ G) := by
    have e : (MonObj.one : 𝟙_ (Over X') ⟶ G) = 1 := by
      rw [Hom.one_def]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, e, one_pow]
  obtain ⟨u₁, hu₁⟩ := exists_lift_torsion n (torsion.ι G n ≫ a)
    (by rw [Category.assoc, ha, ← Category.assoc, hι, MonObj.one_comp])
  obtain ⟨u₂, hu₂⟩ := exists_lift_torsion n (1 : torsion G n ⟶ G)
    (by rw [Hom.one_def, Category.assoc, h0])
  have e₁ : u₁.left ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ a.left := congrArg (·.left) hu₁
  have e₂ : u₂.left ≫ (torsion.ι G n).left = (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
    have := congrArg (·.left) hu₂
    simp only [Hom.one_def, Over.comp_left] at this
    rw [this]
    congr 1
  have := mono_torsion_ι G n
  have key : (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₁.left =
      (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₂.left := by
    refine GlobalTheory.T.eq_of_formallyUnramified_of_eq_at_closedPoint (torsion G n).hom _ _ _ ?_ K (Spec.map (Scheme.stalkClosedPointTo P)) ?_ ?_
    · rw [Category.assoc, Category.assoc, Over.w, Over.w]
    · intro x
      obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact IsLocalRing.comap_closedPoint (Scheme.stalkClosedPointTo P).hom
    · rw [← Category.assoc, ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
        ← cancel_mono (torsion.ι G n).left, Category.assoc, Category.assoc, e₁, e₂, hP]
  rw [← e₁, ← e₂, reassoc_of% key]

theorem exists_valAt : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom] (act : OAct (𝓞 E) G) (I : Ideal (𝓞 E))
    (hex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (P : Sp Ω ⟶ G.left), P ≫ G.hom = x ≫ ℓ →
      (∀ a ∈ I, P ≫ (act.act a).left = P ≫ G.hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) → ∃ c, P = x ≫ w c)
    (K : Type) [Field K] [IsAlgClosed K] (P : Sp K ⟶ (torsion G n).left)
    (hP : ∀ a ∈ I, P ≫ (torsion.ι G n).left ≫ (act.act a).left = P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K), ∃ c, GlobalTheory.TorsSpec.ValAt G n ℓ w (P x) c := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ act I hex K _ _ P hP x
  have := GlobalTheory.GrpTangent.etale_torsion G hn
  have := isDomain_stalk_of_etale (torsion G n).hom (P x)
  obtain ⟨Ω, _, _, y₀, hy₀, _⟩ := GlobalTheory.T.exists_dominant_geometricGenericPoint_spec_domain ((torsion G n).left.presheaf.stalk (P x))
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.exists_lift_geometricGenericPoint_stalk_of_flat (torsion G n).hom (P x) ℓ Ω y₀ hy₀
  have hw' : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w _
  obtain ⟨c, hc⟩ := hex Ω z₀ (y₀ ≫ (torsion G n).left.fromSpecStalk (P x) ≫ (torsion.ι G n).left)
    (by rw [Category.assoc, Category.assoc, hw', hz₀]) (fun a ha => by
      have := act.hom a
      have h := fromSpecStalk_killed G n (act.act a)
        (by rw [← act_natCast act, ← act.mul, ← act.mul, mul_comm]) K P (hP a ha) x
      simp only [Category.assoc]
      rw [h, reassoc_of% hw'])
  refine ⟨c, fun Ω' _ _ y z h => ?_⟩
  exact eq_section_of_isDominant G.hom ℓ _ (w c) (hw c) y₀ z₀ hc y z (by rw [Category.assoc, hw', h])

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsFramePolynomialAtPrimeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clear_denominators_framePolynomial_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 → ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
    ∃ x : 𝓞 z.K, x ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K ((x : z.K) * MvPolynomial.coeff μ G) ≤ 1 := by
  first | exact @GlobalTheory.CoeffDenom.exists_clear_coeff_at_prime | exact GlobalTheory.CoeffDenom.exists_clear_coeff_at_prime | (intros; apply GlobalTheory.CoeffDenom.exists_clear_coeff_at_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenKernelStableHarrisTaylor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_clopen_kerStableAt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ KerStableAt o ψ t := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, he⟩ hB hq
  have hc : IsUnit (c : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [← Nat.cast_pow, map_natCast, ← he] at this
    exact this
  haveI : IsMonHom ψ := hq.1
  haveI : IsMonHom ψ' := hq.2.1
  haveI := D.finO
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := D.O)
  have key : ∀ a : D.O, ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y),
      Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ g : T ⟶ o.A,
        g ^ c = 1 → g ≫ ψ = 1 → g ≫ o.act.act a ≫ ψ = 1 := by
    intro a
    haveI := o.act.hom a
    obtain ⟨W, hW1, hW2, hW, -⟩ := GlobalTheory.LevCover.kerlocus_open_closed Y o.A c Unit (fun _ => B) (fun _ => ψ) B
      (o.act.act a ≫ ψ) o.ab (fun _ => hB) hB (fun _ => inferInstance) inferInstance hc
    refine ⟨W, hW1, hW2, fun Tb t => (hW Tb t).trans ?_⟩
    simp only [forall_const]
  choose W hW1 hW2 hW using key
  have hkill : ∀ (T : Over Y) (g : T ⟶ o.A), g ≫ ψ = 1 → g ^ c = 1 := by
    intro T g hg
    have h1 : g ^ c = g ≫ (𝟙 o.A) ^ c := by rw [MonObj.comp_pow, Category.comp_id]
    rw [h1, ← hq.2.2.1, ← Category.assoc, hg, MonObj.one_comp]
  refine ⟨⋂ a ∈ S, W a, isOpen_biInter_finset (fun a _ => hW1 a),
    isClosed_iInter fun a => isClosed_iInter fun _ => hW2 a, fun Tb t => ?_⟩
  rw [Set.subset_iInter₂_iff]
  constructor
  · intro h T σ hσ g hg a
    let f : D.O →+ Additive (T ⟶ B) := AddMonoidHom.mk' (fun a => Additive.ofMul (g ≫ o.act.act a ≫ ψ))
      (fun a a' => by
        rw [o.act.add]
        haveI := o.act.hom a
        haveI := o.act.hom a'
        rw [MonObj.mul_comp, MonObj.comp_mul]
        rfl)
    have hSk : (S : Set D.O) ⊆ (f.toIntLinearMap.ker : Set D.O) := fun a ha => by
      have := (hW a Tb t).1 (h a ha) T σ hσ g (hkill T g hg) hg
      simp [f, this]
    have htop : (⊤ : Submodule ℤ D.O) ≤ LinearMap.ker f.toIntLinearMap := by
      rw [← hS]; exact Submodule.span_le.mpr hSk
    have ha : f a = 0 := htop Submodule.mem_top
    simpa [f] using ha
  · intro h a _
    exact (hW a Tb t).2 fun T σ hσ g _ hg => h T σ hσ g hg a

end GlobalTheory.UPel.HT.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmFieldTraceFormGramMatrixPosDefStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmField_traceForm_gram_matrix_posDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : 𝓞 E →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m ∧ B0.transpose = B0 ∧ (B0.map (Int.cast : ℤ → ℝ)).PosDef ∧ ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (H.bar a) := by
  first | exact @GlobalTheory.TraceLattice.exists_traceForm_matrix | exact GlobalTheory.TraceLattice.exists_traceForm_matrix | (intros; apply GlobalTheory.TraceLattice.exists_traceForm_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundarySndTr
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CocInv

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

def affVal (V : A.left.affineOpens) (P : GPt A) (h : P.In V.1) : (Pt.aff (A.hom ≫ 𝟙 (Sp K)) V).Hom P where
  ρ := { (GlobalTheory.Points.valMap P.x V.1 (show ⊤ ≤ P.x ⁻¹ᵁ V.1 from h)).hom with
    commutes' := fun r ↦
      (GlobalTheory.Points.valR_eq P.x V.1 h (constFn (A.hom ≫ 𝟙 (Sp K)) V.1 r)).symm.trans
        (GlobalTheory.Points.valR_constFn_of_over _ (algebraMap K P.B) P.x P.w V.1 h r) }
  pt := GlobalTheory.Points.specMap_valMap_fromSpec V.2 P.x h

theorem affVal_ρ (V : A.left.affineOpens) (P : GPt A) (h : P.In V.1) (f : CechDR.Sec (A.hom ≫ 𝟙 (Sp K)) V.1) :
    (affVal V P h).ρ f = valR P.x V.1 f :=
  (GlobalTheory.Points.valR_eq P.x V.1 h f).symm

theorem affVal_comp (V : A.left.affineOpens) {P Q : GPt A} (h : P.In V.1) (φ : P.Hom Q) :
    (affVal V P h).comp φ = affVal V Q (h.map φ) := by
  have e : ((affVal V P h).comp φ).ρ = (affVal V Q (h.map φ)).ρ := by
    ext f
    change φ.ρ ((affVal V P h).ρ f) = _
    rw [affVal_ρ, affVal_ρ, ← φ.pt]
    exact (GlobalTheory.Points.valR_spMap_comp (φ.ρ : P.B →+* Q.B) P.x V.1 h f).symm
  cases h1 : (affVal V P h).comp φ
  cases h2 : affVal V Q (h.map φ)
  rw [h1, h2] at e
  cases e
  rfl

theorem aff_in (V : A.left.affineOpens) : (Pt.aff (A.hom ≫ 𝟙 (Sp K)) V).In V.1 :=
  V.2.fromSpec_preimage_self.ge

def Idx {I : Type} (U : I → A.left.Opens) : Type := {p : I × A.left.affineOpens // p.2.1 ≤ U p.1}

omit [GrpObj A] in

theorem iSup_idx {I : Type} (U : I → A.left.Opens) (hU : ⨆ i, U i = ⊤) : ⨆ a : Idx U, a.1.2.1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ ⨆ i, U i := hU.ge trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    A.left.isBasis_affineOpens.exists_subset_of_mem_open hi (U i).2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(i, ⟨V, hV⟩), hVU⟩, hxV⟩

open Classical in

def βa {I : Type} {U : I → A.left.Opens} (β : ∀ P Q : GPt A, P.Hom Q → Q.B) (a : Idx U) :
    PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  fun P ↦ if h : P.In a.1.2.1 then β _ P (affVal a.1.2 P h) else 0

theorem βa_step {I : Type} {U : I → A.left.Opens} {β : ∀ P Q : GPt A, P.Hom Q → Q.B}
    (hβ : ∀ (P Q T : GPt A) (φ : P.Hom Q) (ψ : Q.Hom T), (∃ i, P.In (U i)) →
      β P T (φ.comp ψ) = ψ.ρ (β P Q φ) + β Q T ψ) (a : Idx U) {P Q : GPt A} (h : P.In a.1.2.1)
    (φ : P.Hom Q) : βa β a Q = φ.ρ (βa β a P) + β P Q φ := by
  have hQ : Q.In a.1.2.1 := h.map φ
  simp only [βa, dif_pos h, dif_pos hQ]
  rw [← affVal_comp a.1.2 h φ]
  exact hβ _ P Q _ φ ⟨a.1.1, (aff_in a.1.2).mono a.2⟩

open Classical in

theorem exists_coboundary_snd_tr : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (I : Type) (U : I → A.left.Opens), ⨆ i, U i = ⊤ → ∀ β : ∀ P Q : GPt A, P.Hom Q → Q.B, (∀ (P Q T : GPt A) (φ : P.Hom Q) (ψ : Q.Hom T), (∃ i, P.In (U i)) → β P T (φ.comp ψ) = ψ.ρ (β P Q φ) + β Q T ψ) → ∀ v : epsR K ⟶ A, IsTangent v → ∃ G : PtFn (A.hom ≫ 𝟙 (Sp K)), ∀ (i : I) (V : A.left.affineOpens), V.1 ≤ U i → ∀ (P Q : GPt A) (φ : P.Hom Q), P.In V.1 → TrivSqZeroExt.snd (R := Q.B) (β (P.tr v) (Q.tr v) (φ.tr v)) = G Q - φ.ρ (G P) := by
  intro K _ A _ hA I U hU β hβ v hv
  let W : Idx U → A.left.Opens := fun a ↦ a.1.2.1

  have hsec : ∀ a b : Idx U, ∃ f : Γ(A.left, W a ⊓ W b), ∀ P : GPt A, P.In (W a ⊓ W b) →
      βa β a P - βa β b P = valR P.x (W a ⊓ W b) f := by
    intro a b
    obtain ⟨f, hf⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K A.left (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ W a ⊓ W b) (W a ⊓ W b)
      (fun _ ↦ le_rfl) (le_iSup (fun _ : Unit ↦ W a ⊓ W b) ()) (fun P ↦ βa β a P - βa β b P) (fun _ P Q φ hP ↦ by
        change βa β a Q - βa β b Q = φ.ρ (βa β a P - βa β b P)
        rw [βa_step hβ a (hP.mono inf_le_left) φ, βa_step hβ b (hP.mono inf_le_right) φ, map_sub]
        ring)
    exact ⟨f, fun P hP ↦ hf () P hP⟩
  choose φab hφab using hsec
  have hcoc : ∀ (a b c : Idx U) (P : GPt A), P.In (W a) → P.In (W b) → P.In (W c) →
      valR P.x _ (φab a b) + valR P.x _ (φab b c) = valR P.x _ (φab a c) := by
    intro a b c P ha hb hc
    rw [← hφab a b P (ha.inf hb), ← hφab b c P (hb.inf hc), ← hφab a c P (ha.inf hc)]
    ring
  obtain ⟨ψ, hψn, hψ⟩ := GlobalTheory.T.derivative_cechCocycle_invariantVectorField_isCoboundary K A hA (Idx U) W (iSup_idx U hU) φab hcoc v hv
  let G : PtFn (A.hom ≫ 𝟙 (Sp K)) := fun P ↦
    if h : ∃ a, P.In (W a) then TrivSqZeroExt.snd (R := P.B) (βa β h.choose (P.tr v)) - ψ h.choose P else 0
  have hG : ∀ (a : Idx U) (P : GPt A), P.In (W a) →
      G P = TrivSqZeroExt.snd (R := P.B) (βa β a (P.tr v)) - ψ a P := by
    intro a P ha
    have h : ∃ a, P.In (W a) := ⟨a, ha⟩
    have hb : P.In (W h.choose) := h.choose_spec
    have e1 := hφab h.choose a (P.tr v) ((hb.inf ha).tr hv)
    have e2 := hψ h.choose a P hb ha
    change βa β h.choose (P.tr v) - βa β a (P.tr v) = valR (P.trx v) _ (φab h.choose a) at e1
    rw [← e1, TrivSqZeroExt.snd_sub] at e2
    simp only [G, dif_pos h]
    linear_combination e2
  refine ⟨G, fun i V hVU P Q φ hP ↦ ?_⟩
  let a : Idx U := ⟨(i, V), hVU⟩
  have hPa : P.In (W a) := hP
  have hQa : Q.In (W a) := hP.map φ
  rw [hG a P hPa, hG a Q hQa, hψn a P Q φ hPa]
  have e := βa_step hβ a (hPa.tr hv) (φ.tr v)
  have e' := congrArg (TrivSqZeroExt.snd (R := Q.B)) e
  change TrivSqZeroExt.snd (R := Q.B) (βa β a (Q.tr v)) =
    TrivSqZeroExt.snd (R := Q.B) (dualAlg φ.ρ (βa β a (P.tr v)) + β (P.tr v) (Q.tr v) (φ.tr v)) at e'
  rw [TrivSqZeroExt.snd_add, snd_dualAlg] at e'
  rw [map_sub]
  linear_combination -e'

end GlobalTheory.CocInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientDataOfNonzeroSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem integral_of_sqPow_bdd (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (y : FractionRing R) (r : R) (hr : r ≠ 0)
    (h : ∀ n : ℕ, ∃ s : R, algebraMap R (FractionRing R) r * y ^ (n ^ 2) = algebraMap R _ s) :
    ∃ s : R, y = algebraMap R _ s := by
  set c : FractionRing R := algebraMap R (FractionRing R) r with hc
  have hc0 : c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  have hall : ∀ k : ℕ, ∃ s : R, c ^ 4 * y ^ k = algebraMap R _ s := by
    intro k
    obtain ⟨p, q, u, v, hk⟩ := Nat.sum_four_squares k
    obtain ⟨s1, h1⟩ := h p
    obtain ⟨s2, h2⟩ := h q
    obtain ⟨s3, h3⟩ := h u
    obtain ⟨s4, h4⟩ := h v
    refine ⟨s1 * s2 * s3 * s4, ?_⟩
    rw [← hk, map_mul, map_mul, map_mul, ← h1, ← h2, ← h3, ← h4, pow_add, pow_add, pow_add]
    ring
  let S : Subalgebra R (FractionRing R) := Algebra.adjoin R {y}
  have hle : Subalgebra.toSubmodule S ≤ Submodule.span R {(c ^ 4)⁻¹} := by
    show Subalgebra.toSubmodule (Algebra.adjoin R {y}) ≤ _
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro z hz
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hz
    obtain ⟨s, hs⟩ := hall k
    have hc4 : c ^ 4 ≠ 0 := pow_ne_zero _ hc0
    have : y ^ k = s • (c ^ 4)⁻¹ := by
      rw [Algebra.smul_def, ← hs]; field_simp
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
  have hfg : (Subalgebra.toSubmodule S).FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span_singleton (R := R) ((c ^ 4)⁻¹ : FractionRing R))
    have h1 : ((Subalgebra.toSubmodule S).comap (Submodule.span R {(c ^ 4)⁻¹}).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Submodule.span R {(c ^ 4)⁻¹}).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  have hint : IsIntegral R y := IsIntegral.of_mem_of_fg S hfg y (Algebra.self_mem_adjoin_singleton R y)
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨s, hs.symm⟩

theorem exists_coefData_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left), GlobalTheory.LN.Cmp φ U U' F → GlobalTheory.LN.CDvr V → Function.Injective φ → (maximalIdeal V).comap φ = maximalIdeal R → GlobalTheory.LN.Under U' U₀.toUnifPre → ∃ (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 ∧ U.ExpT (𝟙_ _) 1 σ f ∧ (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) ∧ GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) ∧ ∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h := by

  intro R _ _ _ hB D A G _ _ U V _ _ _ φ D' A' G' _ _ U' U₀ F C hV hφ hI hU
  obtain ⟨⟨h₁, h₂, -, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hE := GlobalTheory.LN.ega_of_laws h₁ h₂
  have hR : AdmBase R (maximalIdeal R) := hB.1
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  have hmR : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  have := hV.1
  have hV' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hm : maximalIdeal V ≠ ⊤ := (maximalIdeal.isMaximal V).ne_top
  have hIm : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hI.ge
  obtain ⟨σ, hσ0⟩ := GlobalTheory.T.exists_nonzero_section_preUniformised_completeNormal R hB D A G U
  obtain ⟨f, hf, -⟩ := GlobalTheory.CompleteBaseExpansion.main h₁ h₂ hE R _ hR hmR D A G U 1 σ
  obtain ⟨σ', f', hf', hσσ, hff⟩ := GlobalTheory.ExpCmp.expT_cmp R V _ _ φ hIm D D'.toPre A A' G G' U U' F C 1 σ f hf
  have hcmp : GlobalTheory.PsiRing.SecCmp D D'.toPre C.β C.v C.xe f f' := hff
  have hrel' := GlobalTheory.T.psiRel_of_expT' h₁ h₂ V _ hV' D' A' G' U' U₀ hU σ' f' hf'
  have hσ'0 := GlobalTheory.T.pullback_nonzero_section_injective_domain_map R hB D A G U V φ D'.toPre A' G' U' F C hV hφ σ σ' hσσ hσ0
  have hne' : ∀ α, ∃ j, (f' α).f j ≠ 0 :=
    GlobalTheory.T.forall_term_ne_zero_of_psiRelation V D'.toPre f' hrel' (GlobalTheory.T.exists_nonzero_expansionTerm_completeDVR V hV D' A' G' U' U₀ hU σ' f' hf' hσ'0)
  have hne := GlobalTheory.PsiRing.ne_zero_of_secCmp C.pbB.1.w hcmp hne'
  obtain ⟨psi, h, hrel⟩ := GlobalTheory.exists_psi_psiRel h₁ h₂ R D f hne
  let E : DegPre R := GlobalTheory.LN.withPsi D psi h
  have hrelE : GlobalTheory.UU.PsiRel E (𝟙_ _) f := hrel
  have hrig : GlobalTheory.PsiRing.RigCmp φ E D'.toPre C.β C.v := GlobalTheory.T.rigidification_comparison_uniformisation R V _ _ φ hm hIm D D'.toPre A G A' G' U U' F C
  obtain ⟨gam, hgam⟩ := GlobalTheory.PsiRing.exists_generic_map hφ
  have hpsi : GlobalTheory.PsiRing.PsiCmp E D'.toPre C.β C.v C.xe gam :=
    GlobalTheory.T.psiCmp_of_secCmp' R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig f f' hcmp hrelE hrel' (hne' 0) gam hgam
  have hev : E.PsiEven :=
    GlobalTheory.T.psiEven_descend_baseChange h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi D'.psi_even
  have hbi : E.TauBimult :=
    GlobalTheory.T.tauBimult_of_baseChange' h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi D'.tau_bimult
  obtain ⟨ga, a, hS⟩ := GlobalTheory.exists_psiScal R E
  obtain ⟨th, hth, hmul⟩ := GlobalTheory.T.exists_thetaSection_nonzeroFibres_localRing h₂.secTwist R D
  obtain ⟨q, hq⟩ := hmul (f 0)
  choose b hb using fun χ : D.X => GlobalTheory.T.exists_twistedSection_thetaTranslate_coef R D th hmul χ (ga χ) (hS χ).1 (f χ)
  have hab : ∀ χ, algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) (b χ) := fun χ =>
    GlobalTheory.T.psiScalar_eq_expansionCoef_ratio R E ga a f th hS hrelE hth χ q (b χ) hq (hb χ)
  have hq0 : q ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne 0
    apply hj
    rw [GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection R D th (f 0) 0 hq j]
    simp [scal]
  have hint : ∀ χ, ∃ c : R, ((a χ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ c := fun χ => by
    refine integral_of_sqPow_bdd R _ q hq0 fun n => ?_
    obtain ⟨u, hu⟩ := GlobalTheory.T.psiScalar_nsmul_eq_unit_mul_pow_sq R E ga a hS hev hbi χ n
    refine ⟨((u⁻¹ : Rˣ) : R) * b (n • χ), ?_⟩
    rw [map_mul, ← hab, hu]
    have hu1 : algebraMap R (FractionRing R) ((u⁻¹ : Rˣ) : R) * algebraMap R _ (u : R) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap R (FractionRing R) q * ((a χ : (FractionRing R)ˣ) : FractionRing R) ^ (n ^ 2))) * hu1
  choose c hc using hint
  have hbc : ∀ χ, b χ = q * c χ := fun χ => by
    apply IsFractionRing.injective R (FractionRing R)
    exact (hab χ).symm.trans (by rw [map_mul, ← hc χ])
  have hcm : ∀ χ : D.X, χ ≠ 0 → c χ ∈ maximalIdeal R := fun χ hχ => by
    obtain ⟨x, rfl⟩ := C.xe.surjective χ
    obtain ⟨m, hm₁, hm₂⟩ := GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi ga a hS x _
      (D'.psi_pos x fun h0 => hχ (by rw [h0, map_zero])) _ q (hab _)
    have hm₃ : φ q * φ (c (C.xe x)) = φ q * m := by rw [← map_mul, ← hbc]; exact hm₂
    have hφq : φ q ≠ 0 := (map_ne_zero_iff _ hφ).2 hq0
    have e := mul_left_cancel₀ hφq hm₃
    have hmem : c (C.xe x) ∈ (maximalIdeal V).comap φ := Ideal.mem_comap.2 (by rw [e]; exact hm₁)
    exact (Set.ext_iff.1 (congrArg (fun J : Ideal R => (J : Set R)) hI) _).1 hmem
  choose G₁ hG₁ using fun χ : D.X => GlobalTheory.T.exists_translatedThetaCoefficient_section R D th χ (ga χ) (hS χ).1 (c χ)
  choose H₁ hH₁ using fun χ : D.X => GlobalTheory.T.exists_translatedThetaCoefficient_section R D th χ (ga χ) (hS χ).1 1
  classical
  let g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α := fun α => if h0 : α = 0 then h0 ▸ th else G₁ α
  refine ⟨σ, f, g, q, hq0, hf, fun α => ?_, ?_, fun α hα => ⟨c α, hcm α hα, H₁ α, ?_⟩⟩
  · by_cases h0 : α = 0
    · subst h0
      simp only [g, dif_pos rfl]
      exact GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection R D th (f 0) q hq
    · simp only [g, dif_neg h0]
      exact GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional R D α (ga α) th (f α) (G₁ α) (b α) (c α) q (hb α) (hG₁ α) (hbc α)
  · simp only [g, dif_pos rfl]
    exact hth
  · simp only [g, dif_neg hα]
    exact GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional R D α (ga α) th (G₁ α) (H₁ α) (c α) 1 (c α) (hG₁ α) (hH₁ α) (_root_.mul_one _).symm

end GlobalTheory.Mum
end
end

