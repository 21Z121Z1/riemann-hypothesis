import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOverOfGenerated
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGen.Crit

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem asIdeal_p_j (V : Cover Y) (y : V.G) : (V.p (V.j y)).asIdeal = ⊥ := by
  rw [← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]
  change Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥
  have := ((V.π ≫ Y.str) y).isPrime
  rw [Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j (V : Cover Y) {x : V.X} (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
  rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
  change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem j_gen_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h0 : (V.p (genericPoint V.X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans
        (asIdeal_p_j V _).le)
  obtain ⟨y, hy⟩ := mem_range_j V h0
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

theorem nefOver_of_genOver : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p)
    (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (l : ℕ),
    Norms V L f a φ → GenOver V f φ l → NefOver L l := by
  intro F _ _ Y V L f a φ l ⟨r, hr, hu, _, hf⟩ ⟨n, U, s, hUx, hreg, hgen⟩
  haveI := CoverHt.isPreimmersion_j V
  have hη := j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)),
      ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) := fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ (y : Sp (AlgebraicClosure F) ⟶ V.G) (g : V.X.functionField), valAt (y ≫ V.j) g = valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hrg : ∀ (z : V.G) (g : V.X.functionField), RegAt (V.j z) g ↔ RegAt z (ρ g) :=
    fun z g => (SmallSec.regAt_fnMap_iff V.j hη).symm
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr

  let R : L.B.ι → V.X.functionFieldˣ := fun i => Units.map ρ.symm.toMonoidHom (r fun _ => i)
  let s' : V.X → Fin n → V.X.functionField := fun x J => ρ.symm (s x J)
  have eR : ∀ (t : V.G.functionField) (i : L.B.ι), t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField) =
      ρ (ρ.symm t * (R i : V.X.functionField)) := by
    intro t i
    rw [map_mul, ρ.apply_symm_apply]
    exact congrArg _ (ρ.apply_symm_apply _).symm
  have mem_pull : ∀ (z : V.G) (i : L.B.ι), V.j z ∈ L.B.U i → z ∈ (L.B.pull V.j).U (fun _ => i) :=
    fun z i h => Set.mem_iInter.2 fun _ => h

  have split : ∀ (t : V.G.functionField) (i : L.B.ι) (z : V.G), V.j z ∈ L.B.U i →
      t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField) =
        t / V.φ (f (V.π z)) * (V.φ (f (V.π z)) * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) := by
    intro t i z hz
    have h0 : V.φ (f (V.π z)) ≠ 0 := left_ne_zero_of_mul (hu _ _ (mem_pull z i hz)).ne_zero
    field_simp
  have regG : ∀ (t : V.G.functionField) (i : L.B.ι) (z : V.G), V.j z ∈ L.B.U i → RegAt z (t / V.φ (f (V.π z))) →
      RegAt z (t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) := by
    intro t i z hz ht
    rw [split t i z hz]
    exact ht.mul (hu _ _ (mem_pull z i hz)).regAt
  have valG : ∀ (t : V.G.functionField) (i : L.B.ι) (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v)
      (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (hz : z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F))),
      spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U i → RegAt (below z) (t / V.φ (f (V.π (below z)))) →
      e.w (valAt z (t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField))) =
        e.w (valAt z (t / V.φ (f (V.π (below z))))) *
          Real.exp (φ v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩) := by
    intro t i v e z yt hz e₂ hU ht
    have hpt : V.j (below z) ∈ L.B.U i := by
      change (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ _
      rw [← e₂]
      exact hU (Set.mem_univ _)
    have hun := hu _ _ (mem_pull _ i hpt)
    have H : φ v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ =
        Real.log (e.w (valAt z (V.φ (f (V.π (below z))) * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)))) :=
      hf v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt (fun _ => i) rfl e₂ hU
    rw [H, Real.exp_log (e.w.pos (SmallSec.valAt_ne_zero hun)), split t i _ hpt,
      SmallSec.valAt_mul ht hun.regAt, map_mul]
  refine GlobalTheory.T.regular_section_open_cover (𝓞 F) V.X V.p Y.dim V.ar L R hR l n U s' hUx ?_
  intro x i x₀ hx₀ hi₀ hl₀

  have regA : ∀ (J : Fin n) (c : V.X), c ∈ U x → c ∈ L.B.U i → (l : 𝓞 F) ∈ (V.p c).asIdeal →
      RegAt c (s' x J * R i) := by
    intro J c hc hic hlc
    refine GlobalTheory.T.integral_point_place_condition F Y V l (U x ⊓ L.B.U i) _ (fun z hz => ?_) (fun v e z yt hlv hz e₂ hU => ?_) c ⟨hc, hic⟩ hlc
    · rw [hrg, ← eR]
      exact regG _ i z hz.2 (hreg x J z hz.1)
    · have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ U x ⊓ L.B.U i := by
        rw [← e₂]
        exact hU (Set.mem_univ _)
      have hUx' : ⊤ ≤ yt ⁻¹ᵁ U x := fun w hw => (hU hw).1
      have hUi : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun w hw => (hU hw).2
      rw [hv, ← eR, valG _ i v e z yt hz e₂ hUi (hreg x J _ hpt.1)]
      exact (hgen v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt hlv rfl e₂ x hUx').1 J
  refine ⟨fun J => regA J x₀ hx₀ hi₀ hl₀, ?_, ?_⟩
  · obtain ⟨v, e, z, yt, hlv, hz, e₂, hW, hsp, hiff⟩ := GlobalTheory.T.integral_point_closure_extension F Y V l (U x ⊓ L.B.U i) x₀ ⟨hx₀, hi₀⟩ hl₀
    have hcW : yt (IsLocalRing.closedPoint e.O) ∈ U x ⊓ L.B.U i := hW (Set.mem_univ _)
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ U x ⊓ L.B.U i := by
      rw [← e₂]
      exact hW (Set.mem_univ _)
    have hlc : (l : 𝓞 F) ∈ (V.p (yt (IsLocalRing.closedPoint e.O))).asIdeal :=
      (PrimeSpectrum.le_iff_specializes _ _).2 (hsp.map V.p.continuous) hl₀
    have hUx' : ⊤ ≤ yt ⁻¹ᵁ U x := fun w hw => (hW hw).1
    have hUi : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun w hw => (hW hw).2
    obtain ⟨J, hJ⟩ := (hgen v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt hlv rfl e₂ x hUx').2.1
    have hunit : UnitAt (yt (IsLocalRing.closedPoint e.O)) (s' x J * R i) := by
      refine (hiff _ (regA J _ hcW.1 hcW.2 hlc)).1 ?_
      rw [hv, ← eR, valG _ i v e z yt hz e₂ hUi (hreg x J _ hpt.1)]
      exact hJ
    obtain ⟨W', hW', hall⟩ := hunit.exists_nhds
    exact ⟨J, hall x₀ (hsp.mem_open W'.isOpen hW')⟩
  · intro x' hx₀' J hJ
    obtain ⟨W', hW', hall⟩ := hJ.exists_nhds
    obtain ⟨v, e, z, yt, hlv, hz, e₂, hW, hsp, hiff⟩ :=
      GlobalTheory.T.integral_point_closure_extension F Y V l (W' ⊓ (U x ⊓ (U x' ⊓ L.B.U i))) x₀ ⟨hW', hx₀, hx₀', hi₀⟩ hl₀
    have hcW : yt (IsLocalRing.closedPoint e.O) ∈ W' ⊓ (U x ⊓ (U x' ⊓ L.B.U i)) := hW (Set.mem_univ _)
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ W' ⊓ (U x ⊓ (U x' ⊓ L.B.U i)) := by
      rw [← e₂]
      exact hW (Set.mem_univ _)
    have hUx' : ⊤ ≤ yt ⁻¹ᵁ U x := fun w hw => (hW hw).2.1
    have hUx'' : ⊤ ≤ yt ⁻¹ᵁ U x' := fun w hw => (hW hw).2.2.1
    have hUi : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun w hw => (hW hw).2.2.2
    have hc := hall _ hcW.1
    have h1 := (hiff _ hc.regAt).2 hc
    have hlt := (hgen v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt hlv rfl e₂ x hUx').2.2 x' hUx'' J
    have hd : RegAt (below z) ((s x J - s x' J) / V.φ (f (V.π (below z)))) := by
      have hm1 : RegAt (below z) (-1 : V.G.functionField) := ⟨-1, by simp⟩
      rw [show (s x J - s x' J) / V.φ (f (V.π (below z))) =
          s x J / V.φ (f (V.π (below z))) + (-1) * (s x' J / V.φ (f (V.π (below z)))) by ring]
      exact (hreg x J _ hpt.2.1).add (hm1.mul (hreg x' J _ hpt.2.2.1))
    have e₃ : s' x J - s' x' J = ρ.symm (s x J - s x' J) := (map_sub ρ.symm _ _).symm
    rw [e₃, hv, ← eR, valG _ i v e z yt hz e₂ hUi hd] at h1
    change e.w (valAt z ((s x J - s x' J) / V.φ (f (V.π (below z))))) * _ < 1 at hlt
    rw [h1] at hlt
    exact lt_irrefl _ hlt

end GlobalTheory.HtGen.Crit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Uniq

section General

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {J : Type} [Fintype J]

theorem exists_cancel_linComb (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (pr : J → (X' ⟶ X)) (ε : J → ℤ)
    (F : X'' ⟶ X') (pr'' : J → (X'' ⟶ X)) (hpr : ∀ i, pr'' i = F ≫ pr i)
    (w : LB.Iso L' (LB.LinComb L pr ε)) (hw : w.IsGen) (w'' : LB.Iso L'' (LB.LinComb L pr'' ε)) (hw'' : w''.IsGen) :
    ∃ w' : LB.Iso L'' (L'.pull F), PGen w' ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (i : L'.ι) (k : L''.ι),
      f y ∈ LB.wchart L pr'' j → F (f y) ∈ L'.U i → f y ∈ L''.U k →
      gv w'' f y j k = gv w (f ≫ F) y j i * gw w' f y i k := by
  obtain rfl : pr'' = fun i => F ≫ pr i := funext hpr
  have hN := DVR.linComb_isLB L hL pr ε
  have up : ∀ (x : X'') (j : J → L.ι), F x ∈ LB.wchart L pr j → x ∈ LB.wchart L (fun i => F ≫ pr i) j :=
    fun x j h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i
  have down : ∀ (x : X'') (j : J → L.ι), x ∈ LB.wchart L (fun i => F ≫ pr i) j → F x ∈ LB.wchart L pr j :=
    fun x j h => Set.mem_iInter.2 fun i => Set.mem_iInter.1 h i
  let v : LB.Iso L'' ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')) :=
    ⟨fun p => res (fun y hy => ⟨up y _ (mem_pull₂.1 hy.1), hy.2⟩ :
      ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')).U p.1 ⊓ L''.U p.2 ≤
        LB.wchart L (fun i => F ≫ pr i) (p.1 PUnit.unit) ⊓ L''.U p.2) (w''.s (p.1 PUnit.unit, p.2))⟩
  have hv : ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (k : L''.ι), F (f y) ∈ LB.wchart L pr j →
      f y ∈ L''.U k → gw v f y j k = gv w'' f y j k := fun Y f y j k hj hk =>
    gm_res f y _ (show f y ∈ ((LB.LinComb L pr ε).pull (F ≫ 𝟙 X')).U (fun _ => j) ⊓ L''.U k from
      ⟨mem_pull₂.2 hj, hk⟩) _
  have gv' : PGen v := by
    intro Y f y j j' k k' hj hj' hk hk'
    have hj₀ : F (f y) ∈ LB.wchart L pr j := hj
    have hj₀' : F (f y) ∈ LB.wchart L pr j' := hj'
    rw [hv Y f y j k hj₀ hk, hv Y f y j' k' hj₀' hk']
    refine (gm_isGen hw'' f y j j' k k' (up _ _ hj₀) (up _ _ hj₀') hk hk').trans ?_
    refine congrArg (fun a => a * _ * _) ?_
    refine (gm_linComb L _ ε f y j j' (up _ _ hj₀) (up _ _ hj₀')).trans
      (Eq.trans ?_ (gm_linComb L pr ε (f ≫ F ≫ 𝟙 X') y j j' hj₀ hj₀').symm)
    simp only [Category.comp_id, Category.assoc]
  obtain ⟨w', T⟩ := exists_cancel hN (isoPullId w rfl) v (isoPullId_pgen hw rfl) gv' hL' hL''
  refine ⟨w', T.pgen_cancel hN (isoPullId_pgen hw rfl) gv', fun Y f y j i k hj hi hk => ?_⟩
  have e := T Y f y j i k (down _ _ hj) hi hk
  rwa [hv Y f y j k (down _ _ hj) hk, gw_isoPullId w rfl (f ≫ F) y j i (down _ _ hj) hi] at e

theorem gm_mapsAtExp {Y : Scheme.{0}} {pr : J → (X' ⟶ X)} {ε : J → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} {p : Y ⟶ X'}
    {n : ℤ} {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))} (h : MapsAtExp L L' pr ε w p n a b)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (j : J → L.ι) (i : L'.ι) (hj : p (r z) ∈ LB.wchart L pr j)
    (hi : p (r z) ∈ L'.U i) :
    gm r z (LB.wchart L (fun i => p ≫ pr i) j) (b.s j) =
      gv w (r ≫ p) z j i ^ n * gm r z (LB.wchart L' (fun _ : PUnit => p) (fun _ => i)) (a.s (fun _ => i)) := by
  have hm : r z ∈ p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (j, i) := ⟨hj, hi⟩
  have e := congrArg (gm r z _) (h j i)
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ n) (gm_pull r p z _ hm _))

theorem pmaps_of_mapsAtExp (hL : L.IsLB) {pr : J → (X' ⟶ X)} {ε : J → ℤ} {F : X'' ⟶ X'} {pr'' : J → (X'' ⟶ X)}
    (hpr : ∀ i, pr'' i = F ≫ pr i) {w : LB.Iso L' (LB.LinComb L pr ε)} {w'' : LB.Iso L'' (LB.LinComb L pr'' ε)}
    {w' : LB.Iso L'' (L'.pull F)}
    (T : ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : J → L.ι) (i : L'.ι) (k : L''.ι),
      f y ∈ LB.wchart L pr'' j → F (f y) ∈ L'.U i → f y ∈ L''.U k →
      gv w'' f y j k = gv w (f ≫ F) y j i * gw w' f y i k)
    {Y : Scheme.{0}} {p : Y ⟶ X'} {p'' : Y ⟶ X''} (hp : p'' ≫ F = p) {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))}
    {a'' : LB.Gen (LB.LinComb L'' (K := PUnit) (fun _ => p'') (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))}
    {b'' : LB.Gen (LB.LinComb L (K := J) (fun i => p'' ≫ pr'' i) (fun i => n * ε i))}
    (h : MapsAtExp L L' pr ε w p n a b) (h'' : MapsAtExp L L'' pr'' ε w'' p'' n a'' b'')
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι), Good L z I → val b r z I = val b'' r z I) :
    PMaps w' (K := PUnit) (fun _ => p'') (fun _ => p) (fun _ => n) a'' a (𝟙 Y) := by
  obtain rfl : pr'' = fun i => F ≫ pr i := funext hpr
  subst hp
  intro Z r z P Q hP hQ
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have e := H Z r z I hI
  rw [val_of b r z I (fun i => I (r ≫ p'' ≫ F ≫ pr i)) (fun i => by rw [Category.assoc]),
    val_of b'' r z I (fun i => I (r ≫ p'' ≫ F ≫ pr i)) (fun i => rfl)] at e
  have m : ∀ i, pr i (F (p'' (r z))) ∈ L.U (I (r ≫ p'' ≫ F ≫ pr i)) := fun i => hI (r ≫ p'' ≫ F ≫ pr i)
  rw [gm_mapsAtExp h r z _ (P PUnit.unit) (Set.mem_iInter.2 m) (hP PUnit.unit),
    gm_mapsAtExp h'' r z _ (Q PUnit.unit) (Set.mem_iInter.2 m) (hQ PUnit.unit),
    T Z (r ≫ p'') z _ (P PUnit.unit) (Q PUnit.unit) (Set.mem_iInter.2 m) (hP PUnit.unit) (hQ PUnit.unit),
    mul_zpow, Category.assoc, _root_.mul_assoc] at e
  rw [Category.comp_id, Fintype.prod_unique]
  exact mul_left_cancel e

theorem pmaps_of_dense {Y Z₀ : Scheme.{0}} [IsReduced Y] (h : Z₀ ⟶ Y) (z₀ : Z₀)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z₀ ∈ V) {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} {φ' : Y ⟶ X'}
    {φ : Y ⟶ X} (hφ : φ' ≫ F = φ) {a : LB.Gen (L'.pull φ')} {t : LB.Gen (L.pull φ)}
    (H : ∀ (p : L.ι) (q : L'.ι), φ (h z₀) ∈ L.U p → φ' (h z₀) ∈ L'.U q →
      gm h z₀ (LB.wchart L (fun _ : PUnit => φ) (fun _ => p)) (t.s (fun _ => p)) =
        gw w (h ≫ φ') z₀ p q * gm h z₀ (LB.wchart L' (fun _ : PUnit => φ') (fun _ => q)) (a.s (fun _ => q))) :
    PMaps w (K := PUnit) (fun _ => φ') (fun _ => φ) (fun _ => 1) a t (𝟙 Y) := by
  subst hφ
  intro Z r z P Q hP hQ
  let V : Y.Opens := LB.wchart L (fun _ : PUnit => φ' ≫ F) P ⊓ LB.wchart L' (fun _ : PUnit => φ') Q
  have l : V ≤ φ' ⁻¹ᵁ ((L.pull F).U (fun _ => P PUnit.unit) ⊓ L'.U (Q PUnit.unit)) := fun y hy =>
    ⟨mem_pull.2 (Set.mem_iInter.1 hy.1 PUnit.unit), Set.mem_iInter.1 hy.2 PUnit.unit⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V →
      gm r z V (res (inf_le_left : V ≤ _) (t.s P)) = gm r z (LB.wchart L (fun _ : PUnit => φ' ≫ F) P) (t.s P) ∧
      gm r z V (res l (pullU φ' _ (w.s (fun _ => P PUnit.unit, Q PUnit.unit))) * res (inf_le_right : V ≤ _) (a.s Q)) =
        gw w (r ≫ φ') z (P PUnit.unit) (Q PUnit.unit) * gm r z (LB.wchart L' (fun _ : PUnit => φ') Q) (a.s Q) :=
    fun Z r z hz => ⟨gm_res r z _ hz _, (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z l hz _).trans (gm_pull r φ' z _ (l hz) _)) (gm_res r z _ hz _))⟩
  have hz : r z ∈ V := ⟨Set.mem_iInter.2 hP, Set.mem_iInter.2 hQ⟩
  have hz₀ : h z₀ ∈ V := hd V ⟨_, hz⟩
  have e := TauPull.gm_injective_of_dense h z₀ hd V hz₀ ((key _ h z₀ hz₀).1.trans
    ((H (P PUnit.unit) (Q PUnit.unit) (Set.mem_iInter.1 hz₀.1 PUnit.unit) (Set.mem_iInter.1 hz₀.2 PUnit.unit)).trans
      (key _ h z₀ hz₀).2.symm))
  rw [Category.comp_id, Fintype.prod_unique, zpow_one]
  exact (key _ r z hz).1.symm.trans ((congrArg (gm r z V) e).trans (key _ r z hz).2)

end General

variable {R : Type} [CommRing R] [IsDomain R]

theorem xK_zero (D : DegPre R) : D.xK 0 = jK R ≫ eSec D.P.A := by
  have c0 : (D.c 0).left = eSec D.P.A := by
    have := PsiZero.cPoint_zero' D (𝟙_ _)
    rw [DVR.cP, toUnit_unit, Category.id_comp, Hom.one_def, toUnit_unit, Category.id_comp] at this
    rw [this]; rfl
  rw [← c0]; rfl

theorem gm_psi_zero {D : DegPre R} (hB : D.TauBimult) (χ : D.X) (hχ : χ = 0) (y : (TK R).left) (j : D.P.L.ι)
    (hj : eSec D.P.A (jK R y) ∈ D.P.L.U j) :
    gm (𝟙 _) y (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) (fun _ => j)) ((D.psi χ).s (fun _ => j)) =
      (gm (jK R) y (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => j)) (D.rig.s (fun _ => j)))⁻¹ := by
  subst hχ
  have hx := xK_zero D
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (K := PUnit) (fun _ => D.xK 0) (fun _ => j) (fun _ _ _ => rfl)
    (fun k => by rw [hx]; exact hj)
  have e := PsiZero.val_psi_zero hB hJ
  rwa [val_of (D.psi 0) _ y J (fun _ => j) (fun k => (congrArg J (Category.id_comp (D.xK 0))).trans (eJ k)),
    val_of D.rig _ y J (fun _ => j) (fun k => (congrArg J hx.symm).trans (eJ k))] at e

theorem twφ_comp (D₀ D₂ D : DegPre R) (Φ : D₂.P.A ⟶ D₀.P.A) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (i : Fin 3) : twφ D₂ D (Φ ≫ β) b i = Φ.left ≫ twφ D₀ D β b i := by
  have hu : Φ ≫ toUnit D₀.P.A = toUnit D₂.P.A := toUnit_unique _ _
  fin_cases i
  · show (padd D.P.A (Φ ≫ β) (toUnit D₂.P.A ≫ b)).left = (Φ ≫ padd D.P.A β (toUnit D₀.P.A ≫ b)).left
    rw [padd, padd, ← Category.assoc Φ, comp_lift, ← Category.assoc Φ, hu]
  · show (toUnit D₂.P.A ≫ b).left = (Φ ≫ toUnit D₀.P.A ≫ b).left
    rw [← hu, Category.assoc]
  · show (toUnit D₂.P.A ≫ η[D.P.A]).left = (Φ ≫ toUnit D₀.P.A ≫ η[D.P.A]).left
    rw [← hu, Category.assoc]

theorem nonempty_isPullDeg_of_isTwist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D₂ D : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g → Nonempty (IsPullDeg (RingHom.id R) D₀.toPre D₂.toPre) := by
  intro R _ _ _ hR D₀ D₂ D g ⟨β₀, x₀, m₀, c₀, w₀, g₀, ψ₀⟩ ⟨β₂, x₂, m₂, c₂, w₂, g₂, ψ₂⟩
  let Φ : D₂.toPre.P.A ≅ D₀.toPre.P.A := β₂ ≪≫ β₀.symm
  have mΦ : IsMonHom Φ.hom := inferInstanceAs (IsMonHom (β₂.hom ≫ β₀.inv))
  have hβ : β₂.hom = Φ.hom ≫ β₀.hom := by simp [Φ]
  have gp : IsGrpPullback D₂.toPre.P.A D₀.toPre.P.A (specOf (RingHom.id R)) Φ.hom.left :=
    (isGrpPullback_of_iso Φ).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D₀.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) = Φ.hom.left := hF
  have hpr : ∀ i, twφ D₂.toPre D.toPre β₂.hom g.b i =
      (e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R))) ≫ twφ D₀.toPre D.toPre β₀.hom g.b i :=
    fun i => by rw [hF', hβ]; exact twφ_comp _ _ _ _ _ _ i
  obtain ⟨w, gw', T⟩ := exists_cancel_linComb D.toPre.P.isLB D₀.toPre.P.isLB D₂.toPre.P.isLB _ twε _ _ hpr w₀ g₀ w₂ g₂
  let xe : D₂.toPre.X ≃+ D₀.toPre.X := x₂.trans x₀.symm
  have hxe : ∀ χ, x₀ (xe χ) = x₂ χ := fun χ => x₀.apply_symm_apply _
  have hc : ∀ χ, D₂.toPre.c χ ≫ Φ.hom = D₀.toPre.c (xe χ) := fun χ => by
    rw [← cancel_mono β₀.hom, Category.assoc, ← hβ, c₂, c₀, hxe]
  have hc' : ∀ χ, (D₂.toPre.c χ).left ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      (D₀.toPre.c (xe χ)).left := fun χ => by rw [hF', ← Over.comp_left, hc]
  have hx : ∀ χ, D₂.toPre.xK χ ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      D₀.toPre.xK (xe χ) := fun χ => by
    show (jK R ≫ (D₂.toPre.c χ).left) ≫ _ = jK R ≫ (D₀.toPre.c (xe χ)).left
    rw [Category.assoc, hc']
  have hE : eSec D₂.toPre.P.A ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R)) =
      eSec D₀.toPre.P.A := by
    rw [hF', eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  have hψ : ∀ χ, PMaps w (K := PUnit) (fun _ => D₂.toPre.xK χ) (fun _ => D₀.toPre.xK (xe χ)) (fun _ => -1)
      (D₂.toPre.psi χ) (D₀.toPre.psi (xe χ)) (𝟙 _) := fun χ => by
    obtain ⟨t₀, a₀, b₀⟩ := ψ₀ (xe χ)
    obtain ⟨t₂, a₂, b₂⟩ := ψ₂ χ
    refine pmaps_of_mapsAtExp D.toPre.P.isLB hpr T (hx χ) a₀ a₂ fun Z r z I hI => ?_
    rw [val_corr hI b₀ r, val_corr hI b₂ r]
    have : ∀ a b : D.toPre.X, a = b →
        val (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi a) (LB.pullGen D.toPre.P.L _ _ (g.s a) (toUnit (TK R)).left)) r z I =
        val (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi b) (LB.pullGen D.toPre.P.L _ _ (g.s b) (toUnit (TK R)).left)) r z I := by
      rintro a b rfl; rfl
    exact this _ _ (hxe χ)
  obtain ⟨z₀⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  have hr : PMaps w (K := PUnit) (fun _ => eSec D₂.toPre.P.A) (fun _ => eSec D₀.toPre.P.A) (fun _ => 1)
      D₂.toPre.rig D₀.toPre.rig (𝟙 _) := by
    refine pmaps_of_dense (Z₀ := (TK R).left) (jK R) z₀ (TauPull.jK_mem z₀) hE fun p q hp hq => ?_
    have e := hψ 0 _ (𝟙 _) z₀ (fun _ => p) (fun _ => q)
      (fun _ => by
        show (D₂.toPre.xK 0 ≫ e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf (RingHom.id R))) z₀ ∈ _
        rw [hx, map_zero, xK_zero]; exact hp)
      (fun _ => by rw [xK_zero]; exact hq)
    rw [Category.id_comp, Fintype.prod_unique, gm_psi_zero D₀.tau_bimult _ (map_zero xe) z₀ p hp,
      gm_psi_zero D₂.tau_bimult _ rfl z₀ q hq, Category.id_comp, xK_zero, zpow_neg, zpow_one, ← mul_inv, inv_inj] at e
    exact e
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R _ hR.1 D₀
  obtain ⟨hD, -⟩ := UnifUniq.exists_isPullDeg_id D₀.toPre D₂.toPre W hW ψW e me w ((isGen_iff _).2 gw') hE hr xe hc' hψ
  exact ⟨hD⟩

end GlobalTheory.MumCmp.Uniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoprimeIdeleApproximation
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option autoImplicit false

namespace GlobalTheory.CMVal.NormCongr

variable {K : Type} [Field K] [NumberField K]

theorem natCast_mem_of_prime_dvd (P : HeightOneSpectrum (𝓞 K)) {q : ℕ}
    (hq : q.Prime) (h : q ∣ Ideal.absNorm P.asIdeal) : (q : 𝓞 K) ∈ P.asIdeal := by
  have : Fact q.Prime := ⟨hq⟩
  have := P.isPrime
  have : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ P.asIdeal) q h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : q • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  rw [nsmul_eq_mul] at h1
  have h2 : ((q : ℕ) : 𝓞 K ⧸ P.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

theorem coprime_absNorm_of_not_mem (P : HeightOneSpectrum (𝓞 K)) {k : ℕ} (hk : (k : 𝓞 K) ∉ P.asIdeal) :
    Nat.Coprime (Ideal.absNorm P.asIdeal) k := by
  refine Nat.coprime_of_dvd fun q hq h1 h2 => hk ?_
  obtain ⟨c, rfl⟩ := h2
  rw [Nat.cast_mul]
  exact P.asIdeal.mul_mem_right _ (natCast_mem_of_prime_dvd P hq h1)

theorem val_natCast (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((algebraMap K (Af K) (n : K)) v) = v.valuation K (algebraMap (𝓞 K) K (n : 𝓞 K)) := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← map_natCast (algebraMap (𝓞 K) K) n]

theorem val_natCast_le_one (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((algebraMap K (Af K) (n : K)) v) ≤ 1 := by
  rw [val_natCast]; exact v.valuation_le_one _

theorem val_natCast_lt_one (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (h : (n : 𝓞 K) ∈ v.asIdeal) :
    Valued.v ((algebraMap K (Af K) (n : K)) v) < 1 := by
  rw [val_natCast]; exact (v.valuation_lt_one_iff_mem _).2 h

end GlobalTheory.CMVal.NormCongr

open GlobalTheory.CMVal.IdeleIdeal GlobalTheory.CMVal.Euler in

theorem GlobalTheory.CMVal.NormCongr.absNorm_eq_div_modF : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (k n : ℕ), 0 < n → k ∣ n → ∀ m : K, m ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K) →
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime b k ∧ |((Algebra.norm ℚ m : ℚ) : ℝ)| = b / modF t := by
  intro K _ _ t k n hn hkn m hm hyp
  set p : (Af K)ˣ := Units.map (algebraMap K (Af K)).toMonoidHom (Units.mk0 m hm) with hp
  set a : (Af K)ˣ := t⁻¹ * p with ha
  have haval : (a : Af K) = ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m := by
    simp [ha, hp]
  have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'

  have hdiff : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((a : Af K) v - 1) ≤ Valued.v ((algebraMap K (Af K) (n : K)) v) := by
    intro v
    have h1 := hyp v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
    have e : (a : Af K) - 1 = algebraMap K (Af K) (n : K) *
        (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) := by
      rw [← _root_.mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, _root_.one_mul, haval]
    have e2 : (a : Af K) v - 1 = ((a : Af K) - 1) v := by rw [sub_coord, one_coord]
    rw [e2, e, mul_coord, map_mul]
    exact mul_le_of_le_one_right' h1
  have hint : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((a : Af K) v) ≤ 1 := by
    intro v
    have e : (a : Af K) v = ((a : Af K) v - 1) + 1 := by ring
    rw [e]
    refine (Valued.v.map_add _ _).trans (max_le ?_ (by rw [map_one]))
    exact (hdiff v).trans (NormCongr.val_natCast_le_one v n)
  have hunit : ∀ v : HeightOneSpectrum (𝓞 K), (k : 𝓞 K) ∈ v.asIdeal → Valued.v ((a : Af K) v) = 1 := by
    intro v hk
    have hnv : (n : 𝓞 K) ∈ v.asIdeal := by
      obtain ⟨c, rfl⟩ := hkn
      rw [Nat.cast_mul]; exact v.asIdeal.mul_mem_right _ hk
    have hlt := (hdiff v).trans_lt (NormCongr.val_natCast_lt_one v hnv)
    have e : (a : Af K) v = 1 + ((a : Af K) v - 1) := by ring
    rw [e]
    exact Valuation.map_one_add_of_lt _ hlt

  have hmod : modF p = modF t * modF a := by
    rw [← IdeleModule.modF_mul, ha, _root_.mul_inv_cancel_left]
  have hpr := IdeleModule.modF_princ (Units.mk0 m hm)
  rw [← hp, Units.val_mk0] at hpr
  have hb := modF_eq hint
  refine ⟨Ideal.absNorm (idealOf a), ?_, ?_, ?_⟩
  · have hpos := IdeleModule.modF_pos a
    rw [hb] at hpos
    rcases Nat.eq_zero_or_pos (Ideal.absNorm (idealOf a)) with h0 | h0
    · rw [h0] at hpos; simp at hpos
    · exact h0
  · unfold idealOf
    rw [map_finprod Ideal.absNorm (finite_pow a)]
    refine finprod_induction (fun x : ℕ => Nat.Coprime x k) (Nat.coprime_one_left k)
      (fun x y hx hy => Nat.Coprime.mul hx hy) fun w => ?_
    rw [map_pow]
    rcases Nat.eq_zero_or_pos (ordAt a w) with h0 | h0
    · rw [h0, pow_zero]; exact Nat.coprime_one_left k
    · refine Nat.Coprime.pow_left _ (NormCongr.coprime_absNorm_of_not_mem w fun hk => ?_)
      have h1 := hunit w hk
      have : ordAt a w = 0 := by simp [ordAt, h1]
      omega
  · have htpos := IdeleModule.modF_pos t
    rw [hmod, hb] at hpr
    have e : |((Algebra.norm ℚ m : ℚ) : ℝ)| = (|((Algebra.norm ℚ m : ℚ) : ℝ)|)⁻¹⁻¹ := (inv_inv _).symm
    rw [e, ← hpr, mul_inv, inv_inv, div_eq_mul_inv, _root_.mul_comm]
end

