import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0005
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelCoverDatum

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj GlobalTheory.LevelPairing
open CategoryTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
theorem _root_.GlobalTheory.LevelCoverDatum.pd_pos (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.IsLev) : 0 < d.pd := by
  obtain ⟨-, hM, -⟩ := h
  have h3 := d.l₂.three_le
  rw [hM] at h3
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, mul_zero] at h3
  omega

theorem Mb_ne_bot (l : Level H) : l.Mb ≠ ⊥ := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  intro h
  have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
  have := this (Ideal.subset_span rfl)
  rw [h, Ideal.mem_bot] at this
  exact hM (by exact_mod_cast this)

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in

theorem _root_.GlobalTheory.LevelCoverDatum.half_mul_conj (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.IsLev) :
    d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(d.pd : 𝓞 E)} := by
  obtain ⟨-, hM, -, hMb, -⟩ := h
  have h2 := d.l₂.prod
  rw [hMb, Ideal.map_mul, hM, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    mul_mul_mul_comm, l.prod] at h2
  have hne : Ideal.span {(l.M : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    have := l.three_le
    omega
  exact mul_left_cancel₀ hne h2

theorem half_unique (d d' : DeltaDat Xo c n) (h : d.IsLev) (h' : d'.IsLev) (e : d.l₂ = d'.l₂) :
    d.I = d'.I ∧ d.pd = d'.pd := by
  have hM : 0 < l.M := by have := l.three_le; omega
  refine ⟨mul_left_cancel₀ (Mb_ne_bot l) ?_, Nat.eq_of_mul_eq_mul_left hM ?_⟩
  · rw [← h.2.2.2.1, ← h'.2.2.2.1, e]
  · rw [← h.2.1, ← h'.2.1, e]

theorem isLev_change (d : DeltaDat Xo c n) (h : d.IsLev) (φ : (Fin n → LevQ Dw d.l₂) → c.F)
    (nab : NabV d.Xo₂ d.c₂) : DeltaDat.IsLev { d with φδ := φ, nab₂ := nab } := h

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
set_option synthInstance.maxHeartbeats 200000 in

theorem _root_.GlobalTheory.LevelCoverDatum.isLev_smul (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.IsLev) (a : d.c₂.F) (ha : a ≠ 0) :
    _root_.Formalism.L2.Pj.DeltaDat.IsLev { d with cδ := a • d.cδ } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, Submodule.smul_mem _ a h8, ?_⟩
  intro k _ _ _ y₂
  have hy := h9 k y₂
  simp only [_root_.Formalism.L2.Pj.evR] at hy ⊢
  rw [_root_.Formalism.L2.Pj.evalAt_smul]
  exact mul_ne_zero ((map_ne_zero _).mpr ha) hy

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
theorem _root_.GlobalTheory.LevelCoverDatum.zetaM_cover (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.l₂.M = l.M * d.pd) :
    _root_.Formalism.L2.Pj.zetaM d.c₂ ^ d.pd = d.eF (_root_.Formalism.L2.Pj.zetaM c) := by
  have h3 := d.l₂.three_le
  rw [h] at h3
  have hM : l.M ≠ 0 := fun h0 => by rw [h0, zero_mul] at h3; omega
  have hp : d.pd ≠ 0 := fun h0 => by rw [h0, mul_zero] at h3; omega
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow]
  change ((_root_.Formalism.L2.Pj.zetaM d.c₂ : ℂ)) ^ d.pd = (_root_.Formalism.L2.Pj.zetaM c : ℂ)
  rw [_root_.GlobalTheory.LevelPairing.zetaM_coe, _root_.GlobalTheory.LevelPairing.zetaM_coe, h]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in

theorem _root_.GlobalTheory.LevelCoverDatum.noDelta_w (nab : _root_.Formalism.L2.Pj.NabV Xo c)
    (m : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) (x0 : Fin n → Dw.La) :
    (_root_.Formalism.L2.Pj.noDelta Xo c nab m n).w x0 = _root_.Formalism.L2.Pj.x0Dat c x0 := by
  funext q
  apply Subtype.ext
  simp only [_root_.Formalism.L2.Pj.DeltaDat.w, _root_.Formalism.L2.Pj.noDelta, mul_one]
  unfold _root_.Formalism.L2.Pj.x0Dat
  rfl

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in

theorem _root_.GlobalTheory.LevelCoverDatum.noDelta_etaOK (nab : _root_.Formalism.L2.Pj.NabV Xo c)
    (m : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) :
    (_root_.Formalism.L2.Pj.noDelta Xo c nab m n).EtaOK ↔ (∀ a, (Xo.univ.eta a).left ≫ m.φ = (Xo.univ.eta a).left) ∧
      ∀ a, (Xo.univ.etaA a).left ≫ m.φ = (Xo.univ.etaA a).left := by
  simp only [_root_.Formalism.L2.Pj.DeltaDat.EtaOK, _root_.Formalism.L2.Pj.noDelta, Nat.div_self l.A_pos, Category.id_comp]
  refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun a => ?_) <;>
  · apply Iff.of_eq
    congr 3
    open scoped MonObj in exact pow_one _

end GlobalTheory.LevelCoverDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BaseClassMove
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Survey.BaseClassMove

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem latAdm_unit (l : Level H) (bad n : ℕ) : LatAdm l bad (unitLat E n) := by
  have ht : ∀ m, (unitLat E n).TrivAt m := fun m => ⟨1, by simp, by simp [unitLat], by simp [unitLat]⟩
  refine ⟨fun v => ⟨fun hv w hw => ?_, fun hv => ?_⟩, ht _, ht _⟩
  · refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_
    · obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hv j trivial)
      exact ⟨H.bar a, by rw [← ha]; exact H.bar_eq a⟩
    · obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hw j trivial)
      exact ⟨a, ha⟩
  · intro j _
    have h := hv (Pi.single j 1) (fun i _ => by
      by_cases hi : i = j
      · subst hi; simpa using Submodule.one_le.1 le_rfl
      · simp [Pi.single_eq_of_ne hi])
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    obtain ⟨a, ha⟩ := h
    refine Submodule.mem_one.2 ⟨H.bar a, ?_⟩
    have := H.bar_eq a
    change ((H.bar a : 𝓞 E) : E) = v j
    rw [this]
    change IsCMField.complexConj E (algebraMap _ _ a) = _
    rw [ha, IsCMField.complexConj_apply_apply]

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem shortValAt_beta (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F)
    (hβ : β ≠ 0) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (v : S) :
    ShortValAt Xo c nab w Λ β N P y v ↔ ShortValAt Xo c nab w Λ 1 N P y (algebraMap c.F S β * v) := by
  have key : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (a b d : c.F) (T : S'),
      φ v = algebraMap c.F S' (β⁻¹ * a * b * d) * T ↔
        φ (algebraMap c.F S β * v) = algebraMap c.F S' (1⁻¹ * a * b * d) * T := by
    intro S' _ _ φ a b d T
    have hu : algebraMap c.F S' β * algebraMap c.F S' β⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hβ, map_one]
    simp only [map_mul, AlgHom.commutes, inv_one, map_one]
    constructor
    · intro h; rw [h]; linear_combination (algebraMap c.F S' a * algebraMap c.F S' b * algebraMap c.F S' d * T) * hu
    · intro h; linear_combination (algebraMap c.F S' β⁻¹) * h - φ v * hu
  constructor
  · rintro ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).1 h7⟩
  · rintro ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).2 h7⟩

theorem isBeta_unit (n : ℕ) : IsBeta Dw c (unitLat E n) 1 := by
  have e : (unitLat E n).Ln = (unitLat E n).La := inf_idem _
  refine ⟨one_ne_zero, ?_, fun σ => ?_⟩
  · unfold BetaIs; rw [e, ← Submodule.one_eq_span, one_mul]
  · rw [e]; simp

theorem zetaM_pow : zetaM c ^ l.M = 1 := by
  have hM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  unfold zetaM
  rw [← pow_mul, Nat.div_mul_cancel hM]
  apply Subtype.ext
  exact (Complex.isPrimitiveRoot_exp l.M' h0).pow_eq_one

end GlobalTheory.Survey.BaseClassMove
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.CarriedGeneratorUnique
section
noncomputable section

namespace GlobalTheory.LevelMoveTest

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem pinned_isIso {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (x : Sp S ⟶ Xo.X) (pm : Gx x ⟶ Gx (x ≫ ρ))
    (hf : pm ≫ (fst (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hs : pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ) :
    IsIso pm := by
  have p1 : IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left Xo.univ.t.G.hom x :=
    (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip
  have p2 : IsPullback (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left (fst (Over.mk (x ≫ ρ)) Xo.univ.t.G).left
      Xo.univ.t.G.hom (x ≫ ρ) := (IsPullback.of_hasPullback (x ≫ ρ) Xo.univ.t.G.hom).flip
  have p3 := p1.paste_horiz ν.cart.1
  have : pm = (p3.isoIsPullback _ _ p2).hom := by
    apply p2.hom_ext
    · rw [hs]; simp
    · rw [hf]; simp
  rw [this]; infer_instance

theorem carried_generator_unique {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (x : Sp S ⟶ Xo.X) (pm : Gx x ⟶ Gx (x ≫ ρ))
    (hf : pm ≫ (fst (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hs : pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ)
    (s' s'' : LB.Sec (PPx (x ≫ ρ)))
    (h : ∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx x).Opens),
        W = (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ
          ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) →
        ∀ (h₁ : W ≤ pm ⁻¹ᵁ (PPx (x ≫ ρ)).U (fun _ => i)),
        (pm.appLE ((PPx (x ≫ ρ)).U (fun _ => i)) W h₁).hom (s'.f (fun _ => i)) =
        (pm.appLE ((PPx (x ≫ ρ)).U (fun _ => i)) W h₁).hom (s''.f (fun _ => i)))
    (i : Xo.univ.t.PP.L.ι) : s'.f (fun _ => i) = s''.f (fun _ => i) := by
  haveI := pinned_isIso ν x pm hf hs
  have inj : Function.Injective (pm.app ((PPx (x ≫ ρ)).U (fun _ => i))).hom :=
    (ConcreteCategory.bijective_of_isIso (pm.app ((PPx (x ≫ ρ)).U (fun _ => i)))).1
  apply inj
  let W : Xo.univ.t.PP.L.ι → (Gx x).Opens := fun j => (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ
          ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j))
  have hW : ∀ j, W j ≤ pm ⁻¹ᵁ (PPx (x ≫ ρ)).U (fun _ => i) := fun j =>
    GlobalTheory.LevActCompare.overlap_le_tgt ν.cm.F pm hs i j
  refine (Gx x).sheaf.eq_of_locally_eq' W _ (fun j => homOfLE (hW j)) ?_ _ _ ?_
  · intro z hz
    have hc : (snd (Over.mk x) Xo.univ.t.G).left.base z ∈ (⨆ j, Xo.univ.t.PP.L.U j) := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_, hj⟩
    refine Set.mem_iInter.2 fun _ => ?_
    have h1 : (pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left).base z ∈ (Xo.univ.t.PP.L.U i : Set _) :=
      Set.mem_iInter.1 hz 0
    rw [hs] at h1
    exact h1
  · intro j
    exact h i j _ rfl (hW j)

theorem frMove_unique {S : Type} [CommRing S] [Algebra c.F S] {ρ : Xo.X ⟶ Xo.X}
    (ν : SABMap Xo.univ.t Xo.univ.t ρ) (hw : ∀ w w', CubIso ν w → CubIso ν w' → w = w')
    (y y' y'' : FrPt Xo c S) (h' : FrMove ρ ν y y') (h'' : FrMove ρ ν y y'') : y' = y'' := by
  obtain ⟨x', o', u', t', e', b', s', g'⟩ := y'
  obtain ⟨x'', o'', u'', t'', e'', b'', s'', g''⟩ := y''
  obtain ⟨hx, hu, pm, w, hf, hs, hc, h⟩ := h'
  obtain ⟨hx2, hu2, pm2, w2, hf2, hs2, hc2, h2⟩ := h''
  dsimp only at hx hu hf hs h hx2 hu2 hf2 hs2 h2 pm pm2
  subst hx hx2
  obtain rfl := hw w w2 hc hc2
  have p2 : IsPullback (snd (Over.mk (y.x ≫ ρ)) Xo.univ.t.G).left (fst (Over.mk (y.x ≫ ρ)) Xo.univ.t.G).left
      Xo.univ.t.G.hom (y.x ≫ ρ) := (IsPullback.of_hasPullback (y.x ≫ ρ) Xo.univ.t.G.hom).flip
  obtain rfl : pm = pm2 := p2.hom_ext (hs.trans hs2.symm) (hf.trans hf2.symm)
  obtain rfl : u' = u'' := by funext τ i; rw [hu, hu2]
  have hs' : s' = s'' := by
    have key := carried_generator_unique ν y.x pm hf hs s' s'' (fun i j W hW h₁ => by
      subst hW
      exact (h i j _ rfl le_rfl h₁ (GlobalTheory.LevActCompare.levelAction_overlap_le_source_chart ν.cm.F y.x i j)).trans
        (h2 i j _ rfl le_rfl h₁ (GlobalTheory.LevActCompare.levelAction_overlap_le_source_chart ν.cm.F y.x i j)).symm)
    obtain ⟨f', c'⟩ := s'
    obtain ⟨f'', c''⟩ := s''
    obtain rfl : f' = f'' := by
      funext i
      have : i = fun _ => i 0 := funext fun k => congrArg i (Subsingleton.elim _ _)
      rw [this]
      exact key (i 0)
    rfl
  subst hs'
  rfl

end GlobalTheory.LevelMoveTest
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.FlatGenInjective
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntChartCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem isIntPS_iff (T : CDVR) {n d : ℕ} (f : Germ.PS T.Fr n d) :
    IsIntPS T f ↔ ∃ g : Germ.PS T.V n d, f = MvPowerSeries.map (algebraMap T.V T.Fr) g := by
  constructor
  · intro h
    choose a ha using h
    exact ⟨a, MvPowerSeries.ext fun e => (ha e).symm.trans (MvPowerSeries.coeff_map _ _ _).symm⟩
  · rintro ⟨g, rfl⟩ e
    exact ⟨MvPowerSeries.coeff e g, (MvPowerSeries.coeff_map _ _ _).symm⟩

theorem flatGen_injective {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X')) (ε : K → ℤ) (a b : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε))
    (h : flatGen L F φ ε a = flatGen L F φ ε b) : a = b := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  congr 1
  funext j
  have h1 := congrFun (congrArg LB.Gen.s h) (fun k _ => j k)
  have hU : LB.wchart (L.pull F) φ (fun k _ => j k) = LB.wchart L (fun k => φ k ≫ F) j := by
    refine le_antisymm (wchart_pull_le L F φ _) ?_
    intro y hy
    refine Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => ?_
    exact Set.mem_iInter.1 hy k
  have h2 := congrArg (res hU.ge) h1
  have key : ∀ u : Γ(Y, LB.wchart L (fun k => φ k ≫ F) j)ˣ,
      res hU.ge (res hU.le u) = u := fun u => by
    ext
    simp only [res, Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply, ← Functor.map_comp]
    erw [show ((homOfLE hU.le).op ≫ (homOfLE hU.ge).op) = 𝟙 _ from Subsingleton.elim _ _, Y.presheaf.map_id]
    rfl
  exact (key (a j)).symm.trans (h2.trans (key (b j)))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem series_integral (C : IntegralChartA3 Xo c T io y) :
    letI := io.toAlgebra
    (∀ j, IsIntPS T (C.ch.B.G.F j)) ∧ (∀ a j, IsIntPS T (C.ch.B.A.act a j)) ∧ IsIntPS T C.ch.B.ph1 ∧
      IsIntPS T C.ch.B.ph2 ∧ IsIntPS T C.ch.B.sy ∧ ∀ a, IsIntPS T (C.ch.B.ad a) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, -⟩, -⟩ := C.gen
  exact ⟨fun j => (isIntPS_iff T _).2 ⟨_, h1 j⟩, fun a j => (isIntPS_iff T _).2 ⟨_, h2 a j⟩,
    (isIntPS_iff T _).2 ⟨_, h3⟩, (isIntPS_iff T _).2 ⟨_, h4⟩, (isIntPS_iff T _).2 ⟨_, h5⟩,
    fun a => (isIntPS_iff T _).2 ⟨_, h6 a⟩⟩

theorem const_zero (C : IntegralChartA3 Xo c T io y) :
    (∀ j, MvPowerSeries.constantCoeff (C.FT j) = 0) ∧ ∀ a j, MvPowerSeries.constantCoeff (C.actT a j) = 0 := by
  letI := io.toAlgebra
  obtain ⟨⟨h1, h2, -⟩, -⟩ := C.gen
  refine ⟨fun j => ?_, fun a j => ?_⟩
  · have := C.ch.B.G.const j
    rw [h1 j, MvPowerSeries.constantCoeff_map] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this
  · have := C.ch.B.A.const a j
    rw [h2 a j, MvPowerSeries.constantCoeff_map] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this

theorem dim_eq (C : IntegralChartA3 Xo c T io y) : chD C.ch = Fintype.card (Lt1 Dw) := by
  letI := io.toAlgebra
  let f : (Lt1 Dw → T.Fr) →ₗ[T.Fr] (Fin C.ch.d → T.Fr) :=
    { toFun := fun a j => ∑ ℓ, a ℓ * C.ch.uvec ℓ j
      map_add' := fun a b => by funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r a => by funext j; simp [Finset.mul_sum, _root_.mul_assoc] }
  have hb : Function.Bijective f := (Function.bijective_iff_existsUnique f).2 fun v => by
    obtain ⟨a, ha, hu⟩ := C.ch.chart.basis v
    exact ⟨a, funext ha, fun b hb => hu b (congrFun hb)⟩
  have := (LinearEquiv.ofBijective f hb).finrank_eq
  simpa using this.symm

end GlobalTheory.IntChartCheck
end
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.FrBorDiagUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.FrameRelCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem frBor_diag_unique {S : Type} [CommRing S] [Algebra c.F S] (t t' : Ix Dw → Sˣ) (y y' : FrPt Xo c S)
    (h : FrBor t y y') (h' : FrBor t' y y') : t = t' := by
  obtain ⟨x, xo, u, tn, e, b, s, g⟩ := y
  obtain ⟨x', xo', u', tn', e', b', s', g'⟩ := y'
  obtain ⟨hx, hu, pm, hs, hf, ha⟩ := h
  obtain ⟨-, hu', pm', hs', hf', ha'⟩ := h'
  dsimp only at hx hu hu' pm pm' hs hf ha hs' hf' ha'
  subst hx
  have h1 : pm = 𝟙 _ := by
    apply pullback.hom_ext
    · exact hf.trans (Category.id_comp _).symm
    · exact hs.trans (Category.id_comp _).symm
  have h2 : pm' = 𝟙 _ := by
    apply pullback.hom_ext
    · exact hf'.trans (Category.id_comp _).symm
    · exact hs'.trans (Category.id_comp _).symm
  subst h1; subst h2
  have eid : ∀ i (h : (PPx x').U i ≤ (𝟙 (Gx x')) ⁻¹ᵁ (PPx x').U i),
      Scheme.Hom.appLE (𝟙 (Gx x')) ((PPx x').U i) ((PPx x').U i) h = 𝟙 _ := by
    intro i h
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx x').presheaf.map_id]
    rfl
  funext k
  apply Units.ext
  cases k with
  | none =>
    refine (g s').unique (fun i => ?_) (fun i => ?_)
    · exact (ha i le_rfl).symm.trans (congrArg (fun m => CommRingCat.Hom.hom m _) (eid i le_rfl))
    · exact (ha' i le_rfl).symm.trans (congrArg (fun m => CommRingCat.Hom.hom m _) (eid i le_rfl))
  | some k =>
    obtain ⟨τ, i⟩ := k
    obtain ⟨cf, h1, -, h3⟩ := hu τ i
    obtain ⟨cf', h1', -, h3'⟩ := hu' τ i
    have := (b τ (u' τ i) (tn' τ i) (e' τ i)).unique h3 h3'
    rw [← h1, ← h1', this]

end GlobalTheory.FrameRelCheck
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.StandardLatticeGoodPlace
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Survey.StandardLatticeGoodPlace

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.ThetaIntegralityAtPlaces

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mem_std {n : ℕ} (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∀ j, v j ∈ (algebraMap (𝓞 E) E).range := by
  simp [stdLat, Submodule.mem_pi, Submodule.mem_one, RingHom.mem_range]

private theorem algebraMap_range_mem_iff_isIntegral (x : E) : x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem unimod_std (H : Host E) (n : ℕ) : GenLat.Unimod (⟨stdLat E n⟩ : GenLat E n) := by
  intro v
  show v ∈ stdLat E n ↔ ∀ w ∈ stdLat E n, _
  simp only [mem_std]
  constructor
  · intro hv w hw
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (hw j)
    exact (algebraMap_range_mem_iff_isIntegral _).2 (((algebraMap_range_mem_iff_isIntegral _).1 (hv j)).map
      ((IsCMField.complexConj E).toRingEquiv : E →+* E).toIntAlgHom)
  · intro h j
    have hs : ∀ i, (Pi.single j (1 : E) : Fin n → E) i ∈ (algebraMap (𝓞 E) E).range := by
      intro i
      rw [Pi.single_apply]
      split_ifs
      exacts [Subring.one_mem _, Subring.zero_mem _]
    have h1 := h (Pi.single j 1) hs
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true] at h1
    have h2 := ((algebraMap_range_mem_iff_isIntegral _).1 h1).map
      ((IsCMField.complexConj E).toRingEquiv : E →+* E).toIntAlgHom
    exact (algebraMap_range_mem_iff_isIntegral _).2 (by simpa using h2)

theorem trivAt_std (n k : ℕ) : GenLat.TrivAt (⟨stdLat E n⟩ : GenLat E n) k := by
  exact ⟨1, Nat.coprime_one_left _, Submodule.smul_le_right, Submodule.smul_le_right⟩

end GlobalTheory.Survey.StandardLatticeGoodPlace
end
end

