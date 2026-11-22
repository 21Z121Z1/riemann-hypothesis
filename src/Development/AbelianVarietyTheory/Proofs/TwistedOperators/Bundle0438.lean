import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EvRBaseChangeOfFromTest
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsSmulOfMapResidueEqZero
import Formalism.SubspaceCounting.ChoiceOfTopsRefined
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValueAtMultipleOfBaseChangedGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

noncomputable section

namespace GlobalTheory.HkValueMul

theorem fibreSectionScale_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : Formalism.L2.Pj.scal x (0 : S) i = 0 := by
  simp only [Formalism.L2.Pj.scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_zero]

theorem fibreSectionScale_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : Formalism.L2.Pj.scal x (1 : S) i = 1 := by
  simp only [Formalism.L2.Pj.scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem evR_of_secBC_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ (T Ω : Type) [CommRing T] [IsReduced T] [Algebra c.F T] [Field Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (z₀ : FrPt Xo c T) (z₁ : FrPt Xo c Ω) (a₀ : T), z₁.x = spMap χ.toRingHom ≫ z₀.x → (∀ τ j, z₁.u τ j = spMap (dualMap χ.toRingHom) ≫ z₀.u τ j) → SecBC χ.toRingHom a₀ z₀.x z₁.x z₀.s z₁.s → evR Xo c f z₁ = χ (a₀ ^ n * evR Xo c f z₀) := by
  intro E _ _ _ H Dw l Xo c a n f hf T Ω _ _ _ _ _ χ z₀ z₁ a₀ hx hu hs
  have hL := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨w, hw⟩ := hL.bc T Ω χ z₀
  have key : ∃ g : Ωˣ, (g : Ω) = χ a₀ ∧ FrBor (fun i => i.elim g fun _ => 1) w z₁ := by
    have hw' := hw
    obtain ⟨wx, wo, wu, wtan, weig, wbas, ws, wgen⟩ := w
    obtain ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩ := z₁
    obtain ⟨hwx, hwu, pm, hp1, hp2, hp3⟩ := hw'
    dsimp only at hx hu hs hwx hwu hp1 hp2 hp3 ⊢
    subst hx
    subst hwx
    have hSw : GlobalTheory.Frames.SecBC χ.toRingHom 1 z₀.x (spMap χ.toRingHom ≫ z₀.x) z₀.s ws :=
      ⟨pm, hp1, hp2, fun i h => by rw [show Formalism.L2.Pj.scal z₀.x (1 : T) i = 1 from fibreSectionScale_one z₀.x i, _root_.one_mul]; exact hp3 i h⟩
    have hcalc := GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo T Ω Ω χ.toRingHom (RingHom.id Ω) z₀.x
      (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x) rfl (by simp [spMap])
    have hz : ∀ i, zs.f i = Formalism.L2.Pj.scal (spMap χ.toRingHom ≫ z₀.x) (χ a₀) i * ws.f i :=
      (hcalc.2.2.1 a₀ z₀.s ws zs hSw).1 hs
    have hne : χ a₀ ≠ 0 := by
      intro h0
      have hz0 : ∀ i, zs.f i = 0 := fun i => by rw [hz i, h0, show Formalism.L2.Pj.scal (spMap χ.toRingHom ≫ z₀.x) (0 : Ω) i = 0 from fibreSectionScale_zero _ i, MulZeroClass.zero_mul]
      obtain ⟨b, -, hb⟩ := zgen zs
      have e0 := hb 0 (fun i => by rw [hz0 i, MulZeroClass.mul_zero])
      have e1 := hb 1 (fun i => by rw [hz0 i, MulZeroClass.mul_zero])
      exact zero_ne_one (e0.trans e1.symm)
    have hcalc' := GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo Ω Ω Ω (RingHom.id Ω) (RingHom.id Ω)
      (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x) (spMap χ.toRingHom ≫ z₀.x)
      (by simp [spMap]) (by simp [spMap])
    refine ⟨Units.mk0 _ hne, rfl, (GlobalTheory.Frames.frBor_iff_frChg _ _ _).2
      ⟨fun τ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp, rfl, fun τ i => ?_, ?_⟩⟩
    · have e : (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω) i = Pi.single i 1 := by
        ext j
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      show IsCombAt _ (wu τ) ((1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω) i) (zu τ i)
      rw [e, (hu τ i).trans (hwu τ i).symm]
      exact Formalism.L2.PjFree.isCombAt_single (wtan τ) i
    · exact (hcalc'.2.1 _ ws zs).2 (by simpa using hz)
  obtain ⟨g, hg, hb⟩ := key
  rw [GlobalTheory.ArcQ.evR_scale_of_isReduced hL hf χ g z₀ w z₁ hw hb, hg, map_mul, map_pow]

end GlobalTheory.HkValueMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SectionValuePulledBackAlongGroupMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeEx.SvPull

theorem sv_pull_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x₁ : Sp T ⟶ Xo.X} (pm : Gx x₁ ⟶ Gx x) {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)}, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₁) Xo.univ.t.G).left → (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (hi : (PPx x₁).U i ≤ pm ⁻¹ᵁ (PPx x).U i), (pm.appLE _ _ hi).hom (s.f i) = s'.f i) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo S T _ _ x x₁ pm s s' hsnd hf Z r z J hJ
  have hi0 : (PPx x₁).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) ≤
      pm ⁻¹ᵁ (PPx x).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) := by
    intro y hy
    have h1 := Set.mem_iInter.1 hy 0
    change pm.base y ∈ (⋂ k : Fin 1, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹'
      (Xo.univ.t.PP.L.U (J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) : Set _))
    refine Set.mem_iInter.2 fun _ => ?_
    simp only [Set.mem_preimage] at h1 ⊢
    rw [← Scheme.Hom.comp_apply, hsnd]
    exact h1
  have hz : r z ∈ (PPx x₁).U (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left)) :=
    hJ.mem (fun _ : Fin 1 => (snd (Over.mk x₁) Xo.univ.t.G).left) r
  dsimp only [sv]
  rw [sval_of s (r ≫ pm) z J (fun _ => J (r ≫ (snd (Over.mk x₁) Xo.univ.t.G).left))
    (fun _ => by rw [Category.assoc, hsnd])]
  show gs r z ((PPx x₁).U _) (s'.f _) = _
  rw [← hf _ hi0, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, gs_res r z hi0 hz,
    gs_pull r pm z _ (hi0 hz)]
  rfl

end GlobalTheory.HeckeEx.SvPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.SplitCosetCount

section Grp

open Classical

variable {G : Type} [Group G]

theorem card_le_of_isDC {J : Subgroup G} {x : G} {A B : Finset G} (hA : Bridge.IsDC J x A)
    (hB : Bridge.IsDC J x B) : A.card ≤ B.card := by
  classical
  have f : ∀ a ∈ A, ∃ b, b ∈ B ∧ b⁻¹ * a ∈ J := fun a ha => (hB.2 a (hA.1 a ha)).exists
  choose! φ hφB hφJ using f
  refine Finset.card_le_card_of_injOn φ (fun a ha => hφB a ha) ?_
  intro a₁ ha₁ a₂ ha₂ he
  have h1 : a₁⁻¹ * a₂ ∈ J := by
    have h := J.mul_mem (J.inv_mem (hφJ a₁ ha₁)) (hφJ a₂ ha₂)
    have e : ((φ a₁)⁻¹ * a₁)⁻¹ * ((φ a₂)⁻¹ * a₂) = a₁⁻¹ * a₂ := by rw [he]; group
    rwa [e] at h
  exact (hA.2 a₂ (hA.1 a₂ ha₂)).unique ⟨ha₁, h1⟩ ⟨ha₂, by simp⟩

theorem card_eq_of_isDC {J : Subgroup G} {x : G} {A B : Finset G} (hA : Bridge.IsDC J x A)
    (hB : Bridge.IsDC J x B) : A.card = B.card :=
  le_antisymm (card_le_of_isDC hA hB) (card_le_of_isDC hB hA)

variable {H : Type} [Group H] {ρ : G →* H} {S : G → Prop} {K : Set G} {K' : Subgroup H}

theorem lift_isReps (hm : ∀ x y, S x → S y → S (x * y)) (hi : ∀ x, S x → S x⁻¹)
    (hinj : ∀ x y, S x → S y → ρ x = ρ y → x = y) (hK : ∀ g, S g → (g ∈ K ↔ ρ g ∈ K'))
    {g : G} (hg : S g) {R₀ : Finset H} (hR : Formalism.IndefR.Fin.HCount.IsReps K' (ρ g) R₀)
    (ψ : H → G) (hψs : ∀ a, S (ψ a)) (hψ : ∀ a, ρ (ψ a) = a) :
    (∀ γ ∈ R₀.image ψ, ∃ k₁ ∈ {k | k ∈ K ∧ S k}, ∃ k₂ ∈ {k | k ∈ K ∧ S k}, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ {k | k ∈ K ∧ S k}, ∃ k₂ ∈ {k | k ∈ K ∧ S k}, x = k₁ * g * k₂) →
        ∃! γ, γ ∈ R₀.image ψ ∧ γ⁻¹ * x ∈ {k | k ∈ K ∧ S k} := by
  classical
  have hex : ∀ a, ∃ g, S g ∧ ρ g = a := fun a => ⟨ψ a, hψs a, hψ a⟩
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    exact GlobalTheory.SplitPlace.lift_dc hm hex hinj hK hg (hψs a) (by rw [hψ]; exact hR.1 a ha)
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have hx := hm _ _ (hm _ _ hk₁.2 hg) hk₂.2
    have key : ∀ a, (ψ a)⁻¹ * (k₁ * g * k₂) ∈ {k | k ∈ K ∧ S k} ↔ a⁻¹ * ρ (k₁ * g * k₂) ∈ K' := by
      intro a
      have hs := hm _ _ (hi _ (hψs a)) hx
      have := hK _ hs
      rw [map_mul, map_inv, hψ] at this
      exact ⟨fun h => this.1 h.1, fun h => ⟨this.2 h, hs⟩⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := hR.2 (ρ (k₁ * g * k₂)) ⟨_, (hK _ hk₁.2).1 hk₁.1, _, (hK _ hk₂.2).1 hk₂.1,
      by rw [map_mul, map_mul]⟩
    refine ⟨ψ a, ⟨Finset.mem_image_of_mem _ ha, (key a).2 ha'⟩, ?_⟩
    rintro γ ⟨hγ, h⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
    rw [hu b ⟨hb, (key b).1 h⟩]

theorem card_image_section {R₀ : Finset H} (ψ : H → G) (hψ : ∀ a, ρ (ψ a) = a) :
    (R₀.image ψ).card = R₀.card := by
  classical
  refine Finset.card_image_of_injective _ fun a b h => ?_
  rw [← hψ a, ← hψ b, h]

end Grp

theorem gaussBinom_eq (κ : Type) [Field κ] [Fintype κ] (n k : ℕ) :
    Formalism.G0.gaussBinom (Fintype.card κ) n k = GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Fintype.card κ) n k := by
  have h1 := Formalism.G0.Top.subspaceCount (F := κ) (W := Fin n → κ) k
  have h2 := GlobalTheory.GaussCount.subspaceCount κ (Fin n → κ) k
  rw [Module.finrank_fin_fun] at h1 h2
  rw [Nat.card_eq_fintype_card (α := κ)] at h2
  rw [← h1, ← h2]
  unfold Formalism.G0.countBelow
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun U => by simp

end GlobalTheory.SplitCosetCount

namespace GlobalTheory.SplitCosetCount

open Classical
open Formalism.IndefR.Lev GlobalTheory.HeckeParts Formalism.L2.NTheta

set_option maxHeartbeats 1000000 in

theorem card_cosets : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))), Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → k ≤ D.R.r →
    IsHeckeAt (Wc D i) P k α → Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Rc.card = GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm P.asIdeal) D.R.r k := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc hso hk hα hRc
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hF.Sb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  obtain ⟨e, ϖ, he, h1, h2, hαe⟩ := hα
  obtain ⟨Lp, hLp, -, hs, hK⟩ := loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he
  obtain ⟨v, π, s, c1, c2, c3, c4, c5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis (Wc D i) e v π s he.1.1 c2 c3 c4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module (Wc D i)).2
  obtain ⟨hex, hinj⟩ := GlobalTheory.SplitPlace.comp_bij (V := Wc D i) (B := B) he.1 c1 c2
  have hKc := fun g => GlobalTheory.SplitPlace.K_iff (V := Wc D i) (g := g) he.1 c2 c3 hB
  have hu := GlobalTheory.SplitPlace.isUnif he c4 c5 ϖ h1 h2
  obtain ⟨hu0, hu1⟩ := GlobalTheory.SplitPlace.unif_facts hu
  have hH := (GlobalTheory.SplitPlace.hecke_iff he.1 c1 c2 c3 c4 hB hu0 k α).1 hαe

  obtain ⟨w, hw⟩ : ∃ w, π (finPart D (incA D (ϖ : D.host.E))) = w := ⟨_, rfl⟩
  rw [hw] at hu hu0 hu1 hH
  have hirr : Irreducible (⟨w, hu1⟩ : Formalism.UG.Ov D.host.F v) :=
    Formalism.IndefR.Fin.HCount.irreducible_of_unif D.host.F v ⟨w, hu1⟩ hu
  have hv0 : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have htype : Formalism.IndefR.Fin.HCount.IsType (Formalism.UG.Ov D.host.F v) ⟨w, hu1⟩ k
      (GlobalTheory.SplitPlace.comp (Wc D i) π B α) := by
    refine ⟨fun a b => hH.2.1 a b, fun a b => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact hH.2.2.1 a b
    · obtain ⟨d, hd⟩ : ∃ d, (GlobalTheory.SplitPlace.comp (Wc D i) π B α).1.det = d := ⟨_, rfl⟩
      have hdv' := hH.2.2.2
      rw [hd] at hdv'
      have hdv : Valued.v (d / w ^ k) = 1 := by
        rw [map_div₀, map_pow, hdv', div_self (pow_ne_zero _ hv0)]
      have hne : d / w ^ k ≠ 0 := fun h => by rw [h, map_zero] at hdv; exact zero_ne_one hdv
      have hm : d / w ^ k ∈ Formalism.UG.Ov D.host.F v := by show Valued.v ((d / w ^ k : v.adicCompletion D.host.F)) ≤ 1; exact le_of_eq hdv
      have hmi : (d / w ^ k)⁻¹ ∈ Formalism.UG.Ov D.host.F v := by show Valued.v ((d / w ^ k : v.adicCompletion D.host.F)⁻¹) ≤ 1; rw [map_inv₀, hdv, inv_one]
      refine ⟨⟨d / w ^ k, hm⟩, isUnit_iff_exists_inv.2 ⟨⟨_, hmi⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩, ?_⟩
      show _ = w ^ k * (d / w ^ k)
      rw [hd, mul_div_cancel₀ _ (pow_ne_zero _ hu0)]

  obtain ⟨R₀, hR₀⟩ := GlobalTheory.SplitPlace.exists_reps (Formalism.UG.Final.GLintComm D.host.F v (Wc D i).rank)
    (GlobalTheory.SplitPlace.comp (Wc D i) π B α)
  have hc0 := Formalism.IndefR.Fin.HCount.card_reps (Formalism.UG.Ov D.host.F v) hirr htype (R := R₀) hR₀
  choose ψ hψs hψ using hex
  have hl := lift_isReps (ρ := GlobalTheory.SplitPlace.comp (Wc D i) π B) (S := SuppAt e (Wc D i))
    (K := (KsphC (Wc D i) ∅ : Set (GA D (Wc D i)))) (fun _ _ => GlobalTheory.SplitPlace.suppAt_mul)
    (fun _ => GlobalTheory.SplitPlace.suppAt_inv) hinj hKc hH.1 hR₀ ψ hψs hψ
  have hdc : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α (R₀.image ψ) := by
    refine isDC_of_splits hs levG_le_flag ((hLp α).2 hH.1) (fun a ha => ?_) hK hl.1 hl.2
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 ha
    exact (hLp _).2 (hψs b)
  let φ : D.host.E →+* v.adicCompletion D.host.F := (π.comp (finPart D)).comp (incA D)
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, map_mul, c4]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  have hq : Fintype.card (IsLocalRing.ResidueField (Formalism.UG.Ov D.host.F v)) = Ideal.absNorm P.asIdeal := by
    rw [← Nat.card_eq_fintype_card]
    exact GlobalTheory.SplitUnif.card_residueField v φ P c5 hP
  rw [card_eq_of_isDC hRc hdc, card_image_section ψ hψ, hc0, gaussBinom_eq, hq, rank_Wc]

end GlobalTheory.SplitCosetCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibility
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Irr

variable {D : D7}

theorem thPair_self_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (v : VolM D T.rank S.rank) {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) :
    thPair v.μ v.𝓕 f₀ f₀ ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D T.rank S.rank) := i5
  haveI : Countable (ratMx D T.rank S.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, hF, h1⟩ := v.covol
  haveI := hμ
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
  have e : ∀ w, f₀ w * star (f₀ w) = ((‖f₀ w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [Complex.star_def, Complex.mul_conj']; push_cast; rfl
  have hint : Integrable (fun w => ‖f₀ w‖ ^ 2) (v.μ.restrict v.𝓕) :=
    Integrable.of_bound (hf.cont.norm.pow 2).measurable.aestronglyMeasurable (C ^ 2)
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC w) 2)
  intro h0
  have h2 : (∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ) = 0 := by
    have : thPair v.μ v.𝓕 f₀ f₀ = ((∫ w in v.𝓕, ‖f₀ w‖ ^ 2 ∂v.μ : ℝ) : ℂ) := by
      unfold thPair
      simp_rw [e]
      exact integral_ofReal
    rw [this] at h0
    exact_mod_cast h0
  have h3 : ∫⁻ w in v.𝓕, ‖f₀ w‖ₑ ^ 2 ∂v.μ = 0 := by
    have en : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [en]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun w => by positivity), h2,
      ENNReal.ofReal_zero]
  exact hne (GlobalTheory.OrientedHeis.eq_zero_of_lintegral_eq_zero (ratMx D T.rank S.rank) v.μ v.𝓕 hF f₀ hf.cont
    (fun γ hγ w => GlobalTheory.OrientedHeis.theta_norm_periodic hψ hf γ hγ w) h3)

theorem irr : ∀ D : D7, Irr D := by
  intro D ψ hψ S T Γ ℓ hℓ f₀ hf₀ hne hann f hf
  obtain ⟨v⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).2.2.1 T.rank S.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI := v.covol.1
  haveI : SFinite v.μ := inferInstance
  obtain ⟨hint, hmoy⟩ := GlobalTheory.T.moyal_orthogonality_heisenberg_thetaFunctions D ψ hψ S T v f f₀ hf.1 hf₀.1
  have heq : (fun x => ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ) =
      thPair v.μ v.𝓕 f₀ f₀ • f := funext fun x => by rw [hmoy x]; rfl
  have hth : IsThetaFunO ψ S T (fun x => ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ) := by
    rw [heq]; exact GlobalTheory.OrientedHeis.theta_smul _ hf.1
  have hsup := hℓ.sup f₀ hf₀.1 v.μ _ hint hth
  rw [heq, hℓ.smul _ _ hf.1] at hsup
  have hz : ∀ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * ℓ (heisO ψ S T w f₀) = 0 := fun w => by
    by_cases hw : w ∈ Ann ψ S T Γ
    · rw [hann w hw, mul_zero]
    · rw [(GlobalTheory.T.heisenbergVacuumCommutant_preserves_latticeVacua D ψ hψ S T Γ).2.2 v f f₀ hf hf₀ w hw, zero_mul]
  simp_rw [hz, integral_zero] at hsup
  exact (mul_eq_zero.1 hsup).resolve_left (thPair_self_ne_zero hψ v hf₀.1 hne)

end GlobalTheory.Irr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceIsTranslSum
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {K : Type} [CommRing K]

theorem conj_pullback_map (x : Sp K ⟶ Xo.X) (g : Xo.univ.t.G ⟶ Xo.univ.t.G) :
    conj x x ((Over.pullback x).map g).left =
      (lift (fst (Over.mk x) Xo.univ.t.G) (snd (Over.mk x) Xo.univ.t.G ≫ g)).left := by
  refine gx_ext ?_ ?_
  · rw [lift_l_fst]
    exact (over_iff _).2 (pullback.lift_snd _ _ _)
  · rw [lift_l_snd, conj_apply, Category.assoc, Category.assoc, swap_inv_snd, Over.comp_left, ← swap_hom_fst,
      Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

theorem conj_comp_left {x x' x'' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo x' ⟶ Fib Xo x'') :
    conj x x'' (f ≫ g).left = conj x x' f.left ≫ conj x' x'' g.left := by
  simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Over.comp_left]
  simp only [Category.assoc]

theorem conj_id_pow (x : Sp K ⟶ Xo.X) (n : ℕ) :
    conj x x (𝟙 (Fib Xo x) ^ n).left = (mulT Xo.univ.t.G (Over.mk x) n).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G ^ n) = 𝟙 (Fib Xo x) ^ n := by
    have := map_pow (Over.pullback x).homMonoidHom (𝟙 Xo.univ.t.G) n
    rw [← (Over.pullback x).map_id]
    exact this
  rw [← e, conj_pullback_map, MonObj.comp_pow, Category.comp_id, mulT]

theorem conj_id_inv (x : Sp K ⟶ Xo.X) :
    conj x x (𝟙 (Fib Xo x))⁻¹.left = (negT Xo.univ.t.G (Over.mk x)).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G)⁻¹ = (𝟙 (Fib Xo x))⁻¹ := by
    rw [Functor.map_inv', CategoryTheory.Functor.map_id]
  rw [← e, conj_pullback_map, GrpObj.comp_inv, Category.comp_id, negT]
  rfl

theorem negT_comm_conj {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] :
    (negT Xo.univ.t.G (Over.mk x)).left ≫ conj x x' f.left =
      conj x x' f.left ≫ (negT Xo.univ.t.G (Over.mk x')).left := by
  rw [← conj_id_inv, ← conj_id_inv, ← conj_comp_left, ← conj_comp_left, GrpObj.inv_comp, GrpObj.comp_inv,
    Category.id_comp, Category.comp_id]

theorem pow_eq_one_of_mem_transKer_conj {x x' : Sp K ⟶ Xo.X} {f : Fib Xo x ⟶ Fib Xo x'} {f' : Fib Xo x' ⟶ Fib Xo x}
    {n : ℕ} (h : f ≫ f' = 𝟙 _ ^ n) {c : Over.mk x ⟶ Xo.univ.t.G} (hc : c ∈ transKer Xo.univ.t.G (conj x x' f.left)) :
    c ^ n = 1 := by
  rw [← mem_transKer_mulT, mem_transKer, ← conj_id_pow, ← h, conj_comp_left, ← Category.assoc, mem_transKer.1 hc]

theorem thetaTrace_isTranslSum (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x')
    (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K)
    (hf : IsPair (p ^ 2) f f') (hs' : ∀ i, s'.f i = scal x' a i * s₀.f i)
    (h : IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s') :
    ∃ t, IsPullOf p f a s₀ t ∧ IsTranslSum p s t := by
  obtain ⟨β, s₁, t, n, U, F, hβ, hs, ht, hr, hU, hF, hsum⟩ := h
  have := hf.1
  refine ⟨t, ⟨β, s', hβ, hs', ht⟩, n, F, fun i => ?_, hsum⟩
  have hk : (U i).pt ^ (p ^ 2) = 1 := pow_eq_one_of_mem_transKer_conj hf.2.2.1 (hU i).1
  obtain ⟨α₀, α, h₁, h₂, h₃, h₄⟩ := hs
  exact ⟨_, (U i).pt, α₀, α, s₁, U i, rfl, hk, h₁, h₂, h₃, h₄,
    (hU i).symLift hβ.2.1 Xo.univ.t.sym (negT_comm_conj f) hk, hF i⟩

end GlobalTheory.HkIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslationCommutesCanonicalBaseChangeMap
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

theorem translT_comp_isCan : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} (c : Over.mk x ⟶ Xo.univ.t.G) (c₁ : Over.mk x₁ ⟶ Xo.univ.t.G), IsCan χ pm → c₁.left = spMap χ ≫ c.left → (translT Xo.univ.t.G c₁).left ≫ pm = pm ≫ (translT Xo.univ.t.G c).left := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x₁ pm c c₁ h hc
  have hw : pm ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = (Over.mk x₁ ⊗ Xo.univ.t.G).hom := by
    rw [← Over.w (snd (Over.mk x) Xo.univ.t.G), ← Over.w (snd (Over.mk x₁) Xo.univ.t.G), ← Category.assoc, h.2.1]
  let P : Over.mk x₁ ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk pm hw
  let Φ : Over.mk x₁ ⟶ Over.mk x := Over.homMk (spMap χ) h.1.symm
  have hPf : P ≫ fst (Over.mk x) Xo.univ.t.G = fst (Over.mk x₁) Xo.univ.t.G ≫ Φ :=
    Over.OverMorphism.ext (by simpa [P, Φ] using h.2.2)
  have hPs : P ≫ snd (Over.mk x) Xo.univ.t.G = snd (Over.mk x₁) Xo.univ.t.G :=
    Over.OverMorphism.ext (by simpa [P] using h.2.1)
  have hΦ : Φ ≫ c = c₁ := Over.OverMorphism.ext (by simpa [Φ] using hc.symm)
  have key : translT Xo.univ.t.G c₁ ≫ P = P ≫ translT Xo.univ.t.G c := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, hPf, translT, translT, lift_fst, lift_fst_assoc]
      exact hPf.symm
    · rw [Category.assoc, Category.assoc, hPs, translT, translT, lift_snd, lift_snd, translPt, translPt,
        comp_lift_assoc, reassoc_of% hPf, hPs, hΦ]
  have := congrArg CommaMorphism.left key
  simpa [P] using this

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationPlaceByPlaceOnPureTensorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_placeByPlace_on_pureTensors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (g : GA D S) (h : GA D T), {p : Place D | om (gAt S p g, gAt T p h) f₀ ≠ f₀}.Finite → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (om (g⁻¹, h⁻¹) f₀) → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  first | exact @GlobalTheory.PlaceTensor.OmPure.isPure_om | exact GlobalTheory.PlaceTensor.OmPure.isPure_om | (intros; apply GlobalTheory.PlaceTensor.OmPure.isPure_om <;> assumption)
end

