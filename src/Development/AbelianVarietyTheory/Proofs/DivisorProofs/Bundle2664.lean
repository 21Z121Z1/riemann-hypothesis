import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2542
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfCharZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedIdentificationsGenericFibreAgree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GenEqual

theorem key {X₁ X₂ X₃ XE S₁ S₂ S₃ SE : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {L₃ : LB X₃} {LE : LB XE}
    (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (hL₃ : L₃.IsLB) (hLE : LE.IsLB)
    (Fp : X₃ ⟶ X₁) (Φ : X₃ ⟶ X₂) (κ : XE ⟶ X₃)
    (e₁ : S₁ ⟶ X₁) (e₂ : S₂ ⟶ X₂) (e₃ : S₃ ⟶ X₃) (eE : SE ⟶ XE)
    (t₁ : S₃ ⟶ S₁) (t₂ : S₃ ⟶ S₂) (sE : SE ⟶ S₃) (pE : XE ⟶ SE) (hpE : eE ≫ pE = 𝟙 _)
    (hsurj : Function.Surjective pE.appTop.hom) (hc : eE ≫ κ = sE ≫ e₃)
    (r₁ : LB.Gen (L₁.pull e₁)) (r₂ : LB.Gen (L₂.pull e₂)) (r₃ : LB.Gen (L₃.pull e₃)) (rE : LB.Gen (LE.pull eE))
    (wp : LB.Iso L₃ (L₁.pull Fp)) (w : LB.Iso L₃ (L₂.pull Φ)) (F₁ : XE ⟶ X₁) (F₂ : XE ⟶ X₂) (h₁ : κ ≫ Fp = F₁) (h₂ : κ ≫ Φ = F₂) (u₁ : LB.Iso LE (L₁.pull F₁))
    (u₂ : LB.Iso LE (L₂.pull F₂)) (gp : PGen wp) (gw' : PGen w) (g₁ : PGen u₁) (g₂ : PGen u₂)
    (mp : PMaps wp (K := PUnit) (fun _ => e₃) (fun _ => e₁) (fun _ => 1) r₃ r₁ t₁)
    (mw : PMaps w (K := PUnit) (fun _ => e₃) (fun _ => e₂) (fun _ => 1) r₃ r₂ t₂)
    (m₁ : PMaps u₁ (K := PUnit) (fun _ => eE) (fun _ => e₁) (fun _ => 1) rE r₁ (sE ≫ t₁))
    (m₂ : PMaps u₂ (K := PUnit) (fun _ => eE) (fun _ => e₂) (fun _ => 1) rE r₂ (sE ≫ t₂))
    (Z : Scheme.{0}) (f : Z ⟶ XE) (z : Z) (j : L₂.ι) (i : L₃.ι) (k : LE.ι) (l : L₁.ι)
    (hj : F₂ (f z) ∈ L₂.U j) (hi : κ (f z) ∈ L₃.U i) (hk : f z ∈ LE.U k) (hl : F₁ (f z) ∈ L₁.U l) :
    gw w (f ≫ κ) z j i * (gw wp (f ≫ κ) z l i)⁻¹ = gw u₂ f z j k * (gw u₁ f z l k)⁻¹ := by
  subst h₁ h₂
  obtain ⟨v, Tv⟩ := exists_cancel hL₁ wp u₁ gp g₁ hL₃ hLE
  have gv := Tv.pgen_cancel hL₁ gp g₁
  have rv := Tv.pmaps_cancel hL₁ (fun _ => hc) mp m₁
  obtain ⟨u, Tu⟩ := exists_comp hL₃ w v gw' gv hL₂ hLE
  have gu := Tu.pgen_comp hL₃ gw' gv
  have ru := Tu.pmaps_comp hL₃ (fun _ => hc) mw rv
  have e := GlobalTheory.OverMove.gw_eq_of_pmaps hL₂ hLE pE eE hpE hsurj rfl gu g₂ rfl ru m₂ f z j k
  rw [← e, Tu Z f z j i k hj hi hk, Tv Z f z l i k hl hi hk]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem genequal : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w → PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) → ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  intro R R' _ _ _ _ ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ _ hκ hκp hκΦ w hw hr Z f z j i k l hj hi hk hl
  have hs : spMap ((algebraMap R' (FractionRing R')).comp ρ) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
  have m₁ := GlobalTheory.FieldPull.pmaps_rig q₁
  have m₂ := GlobalTheory.FieldPull.pmaps_rig q₂
  rw [hs] at m₁ m₂
  exact key D₁.P.isLB D₂.P.isLB D₃.P.isLB E.P.isLB (GlobalTheory.PsiEvenPull.proj p) Φ κ (eSec D₁.P.A) (eSec D₂.P.A)
    (eSec D₃.P.A) (eSec E.P.A) (spMap ρ) (spMap ρ) (spMap (algebraMap R' (FractionRing R'))) E.P.A.hom
    (Over.w η[E.P.A]) (GlobalTheory.globalFns_holds _ E.P.A E.P.isAb).2 (cubeMapOf hκ).e_comm D₁.rig D₂.rig D₃.rig E.rig
    p.w w _ _ hκp hκΦ q₁.w q₂.w ((isGen_iff _).1 p.w_gen) hw ((isGen_iff _).1 q₁.w_gen) ((isGen_iff _).1 q₂.w_gen)
    (GlobalTheory.FieldPull.pmaps_rig p) hr m₁ m₂ Z f z j i k l hj hi hk hl

end GlobalTheory.GenEqual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCoeffSpanSetSectionsFlatBaseChangeNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem height_comap_eq_one_of_flat_of_mem {R R₁ : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing R₁] [IsNoetherianRing R₁] (ρ : R →+* R₁) (hρ : ρ.Flat) {f : R} (hf : f ≠ 0)
    (q : Ideal R₁) [q.IsPrime] (hq : q.height = 1) (hfq : ρ f ∈ q) : (q.comap ρ).height = 1 := by
  letI := ρ.toAlgebra
  haveI : Module.Flat R R₁ := hρ
  haveI : Algebra.HasGoingDown R R₁ := Algebra.HasGoingDown.of_flat
  haveI : (q.comap ρ).IsPrime := Ideal.comap_isPrime ρ q
  haveI : q.LiesOver (q.comap ρ) := ⟨rfl⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.comap ρ) q
  have hle : (q.comap ρ).height ≤ 1 := by rw [← hq, h]; exact le_self_add
  refine le_antisymm hle ?_
  rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  intro hb
  have : f ∈ q.comap ρ := hfq
  rw [hb, Ideal.mem_bot] at this
  exact hf this

end GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem spanBy_mono {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁) {T T' : Set F₁}
    (h : T ⊆ T') : spanBy c T ⊆ spanBy c T' := by
  rintro v ⟨n, r, t, ht, rfl⟩
  exact ⟨n, r, t, fun i => h (ht i), rfl⟩

theorem spanBy_sections_eq_of_flat : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁) (f : R), f ≠ 0 → ρ.Flat → Function.Injective ρ → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (V₀ : Set F), (0 : F) ∈ V₀ → (∀ a ∈ V₀, ∀ b ∈ V₀, a + b ∈ V₀) → (∀ r, ∀ a ∈ V₀, c₀ r * a ∈ V₀) → (∀ a ∈ V₀, (c₀ f)⁻¹ * a ∈ V₀) → ∀ (W : Ideal R → Set F) (W₁ : Ideal R₁ → Set F₁), (∀ p : Ideal R, p.IsPrime → f ∈ p → ∀ u, ∃ m : ℕ, c₀ f ^ m * u ∈ W p) → (∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → (∀ a ∈ W p, ∀ b ∈ W p, a + b ∈ W p) ∧ (∀ r, ∀ a ∈ W p, c₀ r * a ∈ W p) ∧ (∀ s, s ∉ p → ∀ a ∈ W p, (c₀ s)⁻¹ * a ∈ W p)) → (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → GaussAt c₁ q θ (W (q.comap ρ)) (W₁ q)) → spanBy c₁ (θ '' {u | u ∈ V₀ ∧ ∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → u ∈ W p}) = spanBy c₁ (θ '' V₀) ∩ {v | ∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → v ∈ W₁ q} := by
  intro R R₁ F F₁ _ _ _ _ _ _ _ _ _ _ ρ c₀ c₁ θ f hf hρ hρi hc₀ hcomm hlin V₀ hV0 hVadd hVsmul _ W W₁
    htor hWcl hgauss
  have hW0 : ∀ p : Ideal R, p.IsPrime → f ∈ p → (0 : F) ∈ W p := fun p hp hfp => by
    obtain ⟨m, hm⟩ := htor p hp hfp 0
    simpa using hm
  set P := {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ f ∈ p.asIdeal} with hPdef
  have hP : P.Finite := GlobalTheory.finite_height_eq_one_mem hf

  have key : ∀ S : Finset (PrimeSpectrum R), (∀ p ∈ S, p ∈ P) →
      spanBy c₁ (θ '' {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal}) =
        spanBy c₁ (θ '' V₀) ∩ {x | ∀ p ∈ S, x ∈ spanBy c₁ (θ '' W p.asIdeal)} := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => intro _; ext x; simp
    | insert a S ha ih =>
      intro hS
      have haP := hS a (Finset.mem_insert_self a S)
      obtain ⟨hadd, hsmul, -⟩ := hWcl a.asIdeal a.2 haP.1 haP.2
      have hSP : ∀ p ∈ S, p ∈ P := fun p hp => hS p (Finset.mem_insert_of_mem hp)
      have e : {u | u ∈ V₀ ∧ ∀ p ∈ insert a S, u ∈ W p.asIdeal} =
          {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal} ∩ W a.asIdeal := by
        ext u; simp only [Finset.mem_insert, Set.mem_setOf_eq, Set.mem_inter_iff,
          forall_eq_or_imp]; tauto
      rw [e, GlobalTheory.T.span_image_inter_of_flat_linearlyDisjoint R R₁ F F₁ ρ c₀ c₁ θ hρ hc₀ hcomm hlin {u | u ∈ V₀ ∧ ∀ p ∈ S, u ∈ W p.asIdeal} (W a.asIdeal)
        ⟨hV0, fun p hp => hW0 p.asIdeal p.2 (hSP p hp).2⟩
        (fun a' ha' b hb => ⟨hVadd a' ha'.1 b hb.1, fun p hp =>
          (hWcl p.asIdeal p.2 (hSP p hp).1 (hSP p hp).2).1 a' (ha'.2 p hp) b (hb.2 p hp)⟩)
        (fun r a' ha' => ⟨hVsmul r a' ha'.1, fun p hp =>
          (hWcl p.asIdeal p.2 (hSP p hp).1 (hSP p hp).2).2.1 r a' (ha'.2 p hp)⟩)
        (hW0 a.asIdeal a.2 haP.2) hadd hsmul, ih hSP]
      ext x; simp only [Finset.mem_insert, Set.mem_setOf_eq, Set.mem_inter_iff,
        forall_eq_or_imp]; tauto
  have hS := key hP.toFinset (fun p hp => hP.mem_toFinset.mp hp)
  have e1 : {u | u ∈ V₀ ∧ ∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → u ∈ W p} =
      {u | u ∈ V₀ ∧ ∀ p ∈ hP.toFinset, u ∈ W p.asIdeal} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.Finite.mem_toFinset, hPdef]
    exact and_congr_right fun _ => ⟨fun h p hp => h p.asIdeal p.2 hp.1 hp.2,
      fun h p hp h1 hfp => h ⟨p, hp⟩ ⟨h1, hfp⟩⟩
  rw [e1, hS]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.Finite.mem_toFinset, hPdef]
  refine and_congr_right fun hx => ?_
  have hxr : x ∈ spanBy c₁ (Set.range θ) := spanBy_mono c₁ (Set.image_subset_range θ V₀) hx
  have hd : ∃ d : R₁, d ≠ 0 ∧ c₁ d * x ∈ spanBy c₁ (Set.range θ) := ⟨1, one_ne_zero, by simpa⟩
  constructor
  · intro h q hq hq1 hfq
    have h1 := height_comap_eq_one_of_flat_of_mem ρ hρ hf q hq1 hfq
    refine ((hgauss q hq hq1 hfq) x hd).mpr ⟨1, (Ideal.ne_top_iff_one q).mp hq.ne_top, ?_⟩
    simpa using h ⟨q.comap ρ, Ideal.comap_isPrime ρ q⟩ ⟨h1, hfq⟩
  · intro h p hp
    obtain ⟨hadd, hsmul, hinv⟩ := hWcl p.asIdeal p.2 hp.1 hp.2
    refine GlobalTheory.T.mem_span_image_of_forall_height_one_over_prime R R₁ F F₁ ρ c₀ c₁ θ f hf hρ hρi hc₀ hcomm hlin p.asIdeal p.2 hp.1 hp.2
      (W p.asIdeal) (htor p.asIdeal p.2 hp.2) hadd hsmul hinv x hxr fun q hq hq1 hfq hqp => ?_
    have := ((hgauss q hq hq1 hfq) x hd).mp (h q hq hq1 hfq)
    rwa [hqp] at this

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGeneratedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOn_affineOpen_finitelyGenerated : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → (M.ringOn U).FG := by
  first | exact @GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen | exact GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen | (intros; apply GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointUniqueDegenerationData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.RosUniq
open GlobalTheory.CechPic GlobalTheory.EndRosati

theorem pt_eq_of_cls {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (hK : KTriv A L) {R' : Type} [CommRing R'] {t : Spec (CommRingCat.of R') ⟶ S} (a b : Over.mk t ⟶ A)
    (H : pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ b)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ b).left (cls L hL) =
      pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ a)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ a).left (cls L hL)) : b = a := by
  let T : Over S := Over.mk t
  let x : T ⟶ A := b * a⁻¹
  have hx : lift (fst T A ≫ x) (snd T A) ≫ μ[A] = snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ b) := by
    rw [← Hom.mul_def]
    simp only [x, MonObj.comp_mul, GrpObj.comp_inv]
    ac_rfl
  have hy : snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ a) = snd T A := inv_mul_cancel_right _ _
  rw [hy, ← hx] at H
  have h1 : x = 1 := hK R' t x fun s => by
    obtain ⟨i, hi⟩ := exists_chart hL (a.left s)
    obtain ⟨i', hi'⟩ := exists_chart hL (b.left s)
    let V : (Spec (CommRingCat.of R')).Opens := a.left ⁻¹ᵁ L.U i ⊓ b.left ⁻¹ᵁ L.U i'
    refine ⟨V, ⟨hi, hi'⟩, ?_⟩
    have z : ∀ (c : T ⟶ A) (l : L.ι), V ≤ c.left ⁻¹ᵁ L.U l →
        pull ((fst T A).left ⁻¹ᵁ V).ι (pull (fst T A ≫ c).left (cls L hL)) = 0 := fun c l hl => by
      rw [← pull_comp]
      exact (cls_eq_zero_iff (LB.isLB_pull hL _)).2 (BoxKernel.gen_of_chart (LB.isLB_pull hL _) (fun _ => l)
        fun y => mem_pull.2 (hl y.2))
    have hT : (translDiff A L x).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_zero_iff (LB.isLB_pull hT _)).1 ?_
    refine (cls_pull hT _ _).trans ((congrArg _ (cls_linComb hL _ _ hT)).trans ?_)
    have e : ∑ k : Fin 2, (![1, -1] : Fin 2 → ℤ) k • pull ((![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left,
        (snd T A).left] : Fin 2 → _) k) (cls L hL) =
        pull (fst T A ≫ b).left (cls L hL) - pull (fst T A ≫ a).left (cls L hL) := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      linear_combination (norm := abel) H
    refine (congrArg _ e).trans ?_
    exact (map_sub _ _ _).trans ((congrArg₂ (· - ·) (z b i' inf_le_right) (z a i inf_le_left)).trans (sub_zero _))
  exact mul_inv_eq_one.1 h1

end GlobalTheory.Mum.RosUniq

open GlobalTheory.CechPic GlobalTheory.EndRosati GlobalTheory.Mum.RosUniq in

theorem GlobalTheory.Mum.rosatiAdj_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := by
  intro R _ _ _ _ D f g g' hf hg hg' Hg Hg'
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨r, hr, -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g Hg
  obtain ⟨r', hr', -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g' Hg'
  have key : ∀ {T : Over (Spec (CommRingCat.of R))} (x y : T ⟶ D.toPre.P.A),
      pull (x * (y ≫ g)).left (cls _ D.toPre.P.isLB) - pull (y ≫ g).left (cls _ D.toPre.P.isLB) =
      pull (x * (y ≫ g')).left (cls _ D.toPre.P.isLB) - pull (y ≫ g').left (cls _ D.toPre.P.isLB) :=
    fun x y => by
      have h₁ := cls_of_rosati D.toPre.P.isLB r hr x y
      have h₂ := cls_of_rosati D.toPre.P.isLB r' hr' x y
      linear_combination (norm := abel) h₂ - h₁
  let cv := D.toPre.P.A.left.affineOpenCover
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext cv.openCover _ _ fun j => ?_)
  let t : Spec (CommRingCat.of (cv.X j)) ⟶ Spec (CommRingCat.of R) := cv.f j ≫ D.toPre.P.A.hom
  let y : Over.mk t ⟶ D.toPre.P.A := Over.homMk (cv.f j) rfl
  have k := key (snd (Over.mk t) D.toPre.P.A * (fst _ _ ≫ y ≫ g')⁻¹) (fst (Over.mk t) D.toPre.P.A ≫ y)
  simp only [Category.assoc] at k
  have e := pt_eq_of_cls D.toPre.P.isLB D.toPre.P.ktriv (y ≫ g') (y ≫ g) k
  exact congrArg (·.left) e
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueAddEndomorphismsCubicalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiGenerator_value_add_endomorphisms_cubical : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (cu : CubicalStr A Lr), GlobalFnsSt →
    IsAbelianScheme A →
    ∀ (f₁ g₁ f₂ g₂ f g : A ⟶ A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], f = padd A f₁ f₂ → g = padd A g₁ g₂ →
    ∀ (u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)) (u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε))
      (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)), u₁.IsGen → u₂.IsGen → u.IsGen →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₁ (zero2 A)) (LB.oneGen Lr.L) →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₂ (zero2 A)) (LB.oneGen Lr.L) →
    LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L) →
    ∀ {T : Over S} {z : T.left} {J : (T.left ⟶ A.left) → Lr.L.ι}, Good Lr.L z J → ∀ x y : T ⟶ A,
    val₂ u z J x y * cubV cu z J (y ≫ g₁) (y ≫ g₂) x =
      cubV cu z J (x ≫ f₁) (x ≫ f₂) y * (val₂ u₁ z J x y * val₂ u₂ z J x y) := by
  first | exact @GlobalTheory.RosAddPair.ros_val_padd | exact GlobalTheory.RosAddPair.ros_val_padd | (intros; apply GlobalTheory.RosAddPair.ros_val_padd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueCompEndomorphismsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiGenerator_value_comp_endomorphisms : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}, GlobalFnsSt → IsAbelianScheme A → L.IsLB →
    ∀ (f₁ g₁ f₂ g₂ f g : A ⟶ A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], f = f₂ ≫ f₁ → g = g₁ ≫ g₂ →
    ∀ (u₁ : LB.Gen (LB.LinComb L (rosatiφ A f₁ g₁) rosatiε)) (u₂ : LB.Gen (LB.LinComb L (rosatiφ A f₂ g₂) rosatiε))
      (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)), u₁.IsGen → u₂.IsGen → u.IsGen →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₁ (zero2 A)) (LB.oneGen L) →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u₂ (zero2 A)) (LB.oneGen L) →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) →
    ∀ {T : Over S} {z : T.left} {J : (T.left ⟶ A.left) → L.ι}, Good L z J → ∀ x y : T ⟶ A,
    val₂ u z J x y = val₂ u₁ z J (x ≫ f₂) y * val₂ u₂ z J x (y ≫ g₁) := by
  first | exact @GlobalTheory.rosGen_comp_val | exact GlobalTheory.rosGen_comp_val | (intros; apply GlobalTheory.rosGen_comp_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiStarMulKillsPointOfTrivialPairing
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.CechPic

theorem lam_rosati_field (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O)
    (o : O) {T' : Over (Sp K)} (x z : T' ⟶ P.A) :
    haveI := P.isAb.comm
    lam (cls P.L P.isLB) (x ≫ oA.act (star o)) z = lam (cls P.L P.isLB) x (z ≫ oA.act o) := by
  haveI := P.isAb.comm
  haveI := oA.hom (star o)
  haveI := oA.hom o
  have hr := oA.rosati (star o)
  rw [star_star] at hr
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.globalFns_holds P.isAb P.isLB _ _ hr
  have h := GlobalTheory.EndRosati.cls_of_rosati P.isLB u hu x z
  show _ - _ - _ + _ = _ - _ - _ + _
  rw [h]

theorem kill_of_lam_triv : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O) (e f : O) (H : Over (Sp K)) (a : H ⟶ P.A) (r : P.A ⟶ H), r ≫ a = oA.act e → ∀ (T : Over (Sp K)) (y : T ⟶ P.A), (∃ t : LB.Gen (letI := P.isAb.comm; (abelian₂ P.A P.L).pull (lift (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) : H ⊗ T ⟶ G2 P.A).left), t.IsGen) → y ≫ oA.act (star e * star f) = toUnit T ≫ η[P.A] := by
  intro K _ P O _ _ oA e f H a r hra T y ⟨t, ht⟩
  haveI := P.isAb.comm
  have h0 : lam (cls P.L P.isLB) (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) = 0 := by
    have := (cls_eq_zero_iff (pull_isLB (GlobalTheory.FullSiegel.isLB_lam P.isLB) _)).2 ⟨t, ht⟩
    rwa [GlobalTheory.FullSiegel.cls_lam_pull P.isLB] at this
  have h1 : lam (cls P.L P.isLB) (fst T P.A ≫ y) ((snd T P.A ≫ oA.act e) ≫ oA.act f) = 0 := by
    have := congrArg (pull (lift (snd T P.A ≫ r) (fst T P.A)).left) h0
    rw [pull_lam, map_zero, lift_snd_assoc, lift_fst_assoc, Category.assoc, reassoc_of% hra] at this
    rw [Category.assoc]
    exact this
  have h2 := (lam_rosati_field K P O oA f _ _).trans h1
  have h3 := (lam_rosati_field K P O oA e _ (snd T P.A)).trans h2
  have hb : ((fst T P.A ≫ y) ≫ oA.act (star f)) ≫ oA.act (star e) = fst T P.A ≫ y ≫ oA.act (star e * star f) := by
    rw [oA.map_mul]; simp only [Category.assoc]
  rw [hb] at h3
  have h4 := congrArg (pull (lift (snd P.A T) (fst P.A T)).left) h3
  rw [pull_lam, map_zero, lift_fst_assoc, lift_snd] at h4
  have hg : ∃ t : ((abelian₂ P.A P.L).pull (lift (snd P.A T ≫ y ≫ oA.act (star e * star f)) (fst P.A T)).left).Gen,
      t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB (GlobalTheory.FullSiegel.isLB_lam P.isLB) _)).1 ?_
    rw [GlobalTheory.FullSiegel.cls_lam_pull P.isLB]
    exact h4
  exact (GlobalTheory.FullSiegel.eq_one_of_lam_triv P.isLB P.rigid P.ktriv T _ hg).trans (Hom.one_def ..)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLocalLevelCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_local_level_character : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) (w : BWit q b), q.O.L.sc = K.s → Formalism.IndefR.principalLevelFrame.RowLocPin b.R.T.n.gal.lp w.x.R.θ w.x.Y.PY (w.x.R.MY 0) (fun s => levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 s))) (fun s => Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 s))) (fun _ => w.x.R.e0) w.x.Y.eFT := by
  first | exact @GlobalTheory.Mem.Top.Bl.rowLocPin_bwit | exact GlobalTheory.Mem.Top.Bl.rowLocPin_bwit | (intros; apply GlobalTheory.Mem.Top.Bl.rowLocPin_bwit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameGenericFibreChainRescaledDeeperRealisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sameGenericFibre_chain_rescaled_deeper_realisation : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (D : Deep X₁ ε₁)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A))
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)),
  Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) →
  Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) := by
  first | exact @GlobalTheory.Poinc.same_chain_deep | exact GlobalTheory.Poinc.same_chain_deep | (intros; apply GlobalTheory.Poinc.same_chain_deep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameLineBundleFamilyDescendsFlatSurjectiveQuasiCStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sameLineBundleFamily_descends_flat_surjective_quasiCompact : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (T U Y Y' : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left), Fam A N → Fam A M → ∀ (y : Y ⟶ T) (u : Y ⟶ U) (c : Y' ⟶ Y), Flat c.left → Surjective c.left → QuasiCompact c.left → Same A N M (c ≫ y) (c ≫ u) → Same A N M y u := by
  first | exact @GlobalTheory.DualCon.same_of_fpqc | exact GlobalTheory.DualCon.same_of_fpqc | (intros; apply GlobalTheory.DualCon.same_of_fpqc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfBaseMultipleThetaSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (b : R), GlobalTheory.PsiRing.Mult D th g b → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom b g th := by
  first | exact @GlobalTheory.PsiRing.secIsMul_of_mult | exact GlobalTheory.PsiRing.secIsMul_of_mult | (intros; apply GlobalTheory.PsiRing.secIsMul_of_mult <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfTranslatedThetaCoefficientProportionalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (g₁ g₂ : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ) (b₁ b₂ q : R), GlobalTheory.PsiRing.Coef D χ u th g₁ b₁ → GlobalTheory.PsiRing.Coef D χ u th g₂ b₂ → b₁ = q * b₂ → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q g₁ g₂ := by
  first | exact @GlobalTheory.PsiRing.secIsMul_of_coef | exact GlobalTheory.PsiRing.secIsMul_of_coef | (intros; apply GlobalTheory.PsiRing.secIsMul_of_coef <;> assumption)
end

