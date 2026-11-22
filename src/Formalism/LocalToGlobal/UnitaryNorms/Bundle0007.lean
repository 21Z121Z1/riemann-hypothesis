import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0002

-- bundled from Formalism.LocalToGlobal.UnitaryNorms.CharDiv
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def TupTied.InQ' {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (μ : D.what₂.Tup)
    (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∃ w ∈ aboveF (L := D.host.E) D.host.F v, ¬ (Tp.xi μ).UnrAt w

structure DivisorCharacterCompatibility (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) (Z : DivX D) where
  Qp_iff : ∀ μ p, p ∈ Z.Qp μ ↔ p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w
  eQPl : ∀ μ, Z.QPl μ ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}
  qv_eq : ∀ μ v, Z.qv μ v = Ideal.absNorm (eQPl μ v).1.asIdeal

end Formalism.L2.Host
end
end

-- bundled from Formalism.LocalToGlobal.UnitaryNorms.CharExEta
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

section Gen

variable (L : Type) [Field L] [NumberField L]

theorem mulSupport_ord_finite (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (x : Ideles L) :
    (Function.mulSupport fun v => c v ^ ordAt L v x).Finite := by
  refine (Filter.eventually_cofinite.mp (ordAt_eventually L x)).subset fun v hv h0 => hv ?_
  show c v ^ ordAt L v x = 1
  rw [h0, zpow_zero]

def unrQ (c : HeightOneSpectrum (𝓞 L) → ℂˣ) : Ideles L →* ℂˣ where
  toFun x := ∏ᶠ v, c v ^ ordAt L v x
  map_one' := by simp only [ordAt_one, zpow_zero, finprod_one]
  map_mul' x y := by
    simp only [ordAt_mul, zpow_add]
    exact finprod_mul_distrib (mulSupport_ord_finite L c x) (mulSupport_ord_finite L c y)

variable {L}

theorem unrQ_unit (c : HeightOneSpectrum (𝓞 L) → ℂˣ) {u : Ideles L} (hu : u ∈ unitIdeles L) : unrQ L c u = 1 := by
  show ∏ᶠ v, c v ^ ordAt L v u = 1
  have h : ∀ v, c v ^ ordAt L v u = 1 := fun v => by rw [(ordAt_eq_zero_iff L v u).mpr (hu v), zpow_zero]
  simp only [h, finprod_one]

theorem continuous_of_unit (hO : OpenUnits L) (Φ : Ideles L →* ℂˣ) (h : ∀ u ∈ unitIdeles L, Φ u = 1) : Continuous Φ := by
  refine continuous_of_continuousAt_one Φ ?_
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  exact Filter.mem_of_superset (hO.mem_nhds (one_mem _)) fun u hu => (h u hu).symm

open Classical in

def InfChar {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ) : Prop :=
  ∃ Φ : Ideles L →* ℂˣ, Continuous Φ ∧ (∀ x, ‖((Φ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ v x, Φ (localIdele L v x) = 1) ∧
    (∀ k : Lˣ, ((Φ (diagUnits L k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ∧
    ∀ (S : Finset (InfinitePlace L)) (k : Lˣ), ((Φ (∏ w ∈ S, infIdele L w (atInf w k)) : ℂˣ) : ℂ) =
      ∏ i ∈ Finset.univ.filter (fun i => InfinitePlace.mk (φ i) ∈ S), (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i

end Gen

variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)

def cEta (P : HeightOneSpectrum (𝓞 H.E)) : ℂˣ :=
  if (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 1 then -1 else 1

def etaVal (k : H.Eˣ) : ℂ :=
  ((unrQ H.E (cEta H) (diagUnits H.E k) : ℂˣ) : ℂ) *
    ∏ τ, (embPsi H τ (k : H.E) / ((‖embPsi H τ (k : H.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)

def EtaFinCheck : Prop := ∀ v k, unrQ H.E (cEta H) (aF H.F v k) = etaFin (L := H.E) H.F v k

open Classical in

def EtaInfCheck : Prop := ∀ (w : InfinitePlace H.F) (k : H.Fˣ),
  (∏ i ∈ Finset.univ.filter (fun i => InfinitePlace.mk (embPsi H i) ∈ aboveInf (L := H.E) H.F w),
    (embPsi H i ((upF H.F k : H.Eˣ) : H.E) / ((‖embPsi H i ((upF H.F k : H.Eˣ) : H.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)) =
    ((etaInf H.F w k : ℂˣ) : ℂ)

def EtaGlob : Prop := ∀ k : H.Eˣ, diagUnits H.E k ∈ unitF (L := H.E) H.F → etaVal H k = 1

def GlobForm : Prop := ∀ k : H.Eˣ, diagUnits H.E k ∈ unitF (L := H.E) H.F →
  ∃ a : H.Fˣ, k = upF H.F a ∨ ∃ s : H.Eˣ, (s : H.E) = H.sqrtMinusD ∧ k = s * upF H.F a

def EtaRecF : Prop := ∀ a : H.Fˣ, etaVal H (upF H.F a) = 1

def EtaSqrtD : Prop := ∀ s : H.Eˣ, (s : H.E) = H.sqrtMinusD → etaVal H s = 1

end CharEx

end Formalism.L2.Host
end
end

-- bundled from Formalism.LocalToGlobal.UnitaryNorms.CharGal
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.ConjugateSelfDual ReciprocityTheory.Gal

def toC (D : D7) (i : D.nd.Loc) : D.nd.O i →+* ℂ :=
  ((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))

def IsGalOf (D : D7) (i : D.nd.Loc) (U : Set (PlE D.host)) (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.nd.O i)ˣ) (χ : HChar D.host.E)
    (s : ℝ) : Prop :=
  ∀ w ∈ U, w ∉ placesOver D.host.E (D.nd.l i) → χ.UnrAt w →
    ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) σ →
      toC D i ((r σ : (D.nd.O i)ˣ) : D.nd.O i) = ((χ.val w)⁻¹ : ℂˣ).1 * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)

theorem NCharTied.chi_one {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} (T : NCharTied D C nch Tp)
    (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) :
    IsGalOf D i {w | SplitOut D.nd i w} (D.nd.chi i 1) (Tp.tup (D.nd.mu i) j * C.eta⁻¹)
      (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) := by
  intro w hw _ hU B σ hB hσ
  have hπ : (T.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = Tp.tup (D.nd.mu i) j * C.eta⁻¹ := by
    rw [T.tw, T.muC i j hj, T.etaTinv]
  have hU' : (T.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1.UnrAt w := by
    rw [hπ]
    exact hU
  have hunr : D.naut.unr (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) := (T.unr_iff _ w).2 hU'

  have hc := (D.naut.chi_mu i w hw).2 B σ hB hσ
  rw [D.naut.frobEig_tw _ _ hunr, T.frob _ w hU', Multiset.map_singleton, hπ] at hc
  exact (Multiset.singleton_inj.1 hc).symm

theorem delta_side (D : D7) (a : D.nd.Loc) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (x x' : D.LL0)
    (hx' : (x' : D.what₂.LL) = star (x : D.what₂.LL))
    (h : algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a)))
      ((D.ntw.delta (D.ntw.twOf a) σ : (D.ntw.O0 (D.ntw.twOf a))ˣ) : D.ntw.O0 (D.ntw.twOf a)) = D.ntw.emb0 (D.ntw.twOf a) x) :
    toC D a (D.ntw.twist₂ a ((D.ntw.delta (D.ntw.twOf a) σ : (D.ntw.O0 (D.ntw.twOf a))ˣ) : D.ntw.O0 (D.ntw.twOf a))) =
      if D.ntw.twSide a then D.what₂.embLL (x : D.what₂.LL) else D.what₂.embLL (x' : D.what₂.LL) := by
  by_cases hs : D.ntw.twSide a = true
  · rw [if_pos hs]
    have he := D.ntw.twO_emb a x _ (by rw [if_pos hs]; exact h)
    exact (congrArg (fun t => D.naut.iotaQC a (D.naut.iotaQ a t)) he.symm).trans (D.naut.iota_LL a x)
  · rw [if_neg hs]

    have he := D.ntw.twO_emb a x' _ (by
      rw [if_neg hs, h]
      exact (D.ntw.restX_coefficientEmbedding_conj _ x' x (by rw [hx', star_star])).symm)
    exact (congrArg (fun t => D.naut.iotaQC a (D.naut.iotaQ a t)) he.symm).trans (D.naut.iota_LL a x')

def DeltaRead (D : D7) (C : CharFrame D) : Prop :=
  ∀ (s : D.ntw.Tw) (w : PlE D.host), w ∉ placesOver D.host.E (D.ntw.l s) → (C.delAt (D.ntw.l s)).UnrAt w →
    ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) σ →
      ∃ x : D.LL0, D.what₂.embLL (x : D.what₂.LL) = (((C.delAt (D.ntw.l s)).val w)⁻¹ : ℂˣ).1 ∧
        algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)) ((D.ntw.delta s σ : (D.ntw.O0 s)ˣ) : D.ntw.O0 s) = D.ntw.emb0 s x

theorem CharFrame.delAt_unitary {D : D7} (C : CharFrame D) (l : ℕ) : (C.delAt l).IsUnitary := by

  have key : ∀ χ : HChar D.host.E, (∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) → χ.IsUnitary := by
    rintro χ ⟨n, hn, hχ⟩ x
    have hχ' : χ ^ n = 1 := hχ
    have h1 : (χ.1 x) ^ n = 1 := by
      have := congrArg (fun ψ : HChar D.host.E => ψ.1 x) hχ'
      exact this
    have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2
  unfold CharFrame.delAt
  split
  · exact key _ C.isDel'.fin
  · exact key _ C.isDel.fin

theorem isGalOf_delta_of_deltaRead (D : D7) (C : CharFrame D) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (hrd : DeltaRead D C) (a : D.nd.Loc) :
    IsGalOf D a Set.univ ((Units.map (D.ntw.twist₂ a).toMonoidHom).comp (D.ntw.delta (D.ntw.twOf a)))
      (if D.ntw.twSide a then C.delAt (D.nd.l a) else (C.delAt (D.nd.l a))⁻¹) 0 := by
  intro w _ hw hU B σ hB hσ
  have hl : D.ntw.l (D.ntw.twOf a) = D.nd.l a := D.ntw.twOf_l a

  have conj_inv : ∀ u : ℂˣ, ‖(u : ℂ)‖ = 1 → starRingEnd ℂ ((u⁻¹ : ℂˣ) : ℂ) = (u : ℂ) := by
    intro u hu
    have hn : Complex.normSq (u : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hu, one_pow]
    rw [Units.val_inv_eq_inv_val, map_inv₀, Complex.inv_def, Complex.normSq_conj, hn]
    simp
  have hinv : ((C.delAt (D.nd.l a))⁻¹).val w = ((C.delAt (D.nd.l a)).val w)⁻¹ := rfl
  have hU' : (C.delAt (D.nd.l a)).UnrAt w := by
    by_cases hs : D.ntw.twSide a = true
    · rw [if_pos hs] at hU
      exact hU
    · rw [if_neg hs] at hU
      intro y hy
      have h1 : (((C.delAt (D.nd.l a)).loc w) y)⁻¹ = 1 := hU y hy
      exact inv_eq_one.1 h1
  obtain ⟨x, hxv, hxd⟩ := hrd (D.ntw.twOf a) w (by rw [hl]; exact hw) (by rw [hl]; exact hU') B σ hB hσ
  rw [hl] at hxv
  have hd := delta_side D a σ x ⟨star (x : D.what₂.LL), hstar x⟩ rfl hxd
  show toC D a (D.ntw.twist₂ a ((D.ntw.delta (D.ntw.twOf a) σ : (D.ntw.O0 (D.ntw.twOf a))ˣ) :
    D.ntw.O0 (D.ntw.twOf a))) = _
  rw [hd, Complex.ofReal_zero, Complex.cpow_zero, mul_one]
  by_cases hs : D.ntw.twSide a = true
  · rw [if_pos hs, if_pos hs]
    exact hxv
  · rw [if_neg hs, if_neg hs]
    show D.what₂.embLL (star (x : D.what₂.LL)) = _
    rw [D.starLL_cx, hxv, hinv, inv_inv]
    apply conj_inv
    exact C.delAt_unitary _ _

structure NGalChrTied (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) where

  psi_is : ∀ a, IsPsi (D.nd.l a) (D.nd.Q a) (Tp.psi (D.nd.w a))

  psiL : ∀ a, IsGalOf D a Set.univ (D.ntw.psiL a) (Tp.psi (D.nd.w a)) 0

  deltaRead : DeltaRead D C

theorem NGalChrTied.delta {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} (T : NGalChrTied D C nch Tp)
    (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (a : D.nd.Loc) :
    IsGalOf D a Set.univ ((Units.map (D.ntw.twist₂ a).toMonoidHom).comp (D.ntw.delta (D.ntw.twOf a)))
      (if D.ntw.twSide a then C.delAt (D.nd.l a) else (C.delAt (D.nd.l a))⁻¹) 0 :=
  isGalOf_delta_of_deltaRead D C hstar T.deltaRead a

def PsiChoiceCompatible (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ v : PlE D.host, v ∉ nch.Q w → v ∉ placesOver D.host.E (D.what₂.places.resChar w) →
    ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B v →
      IsFrob (F := D.host.E) B (normV v) σ → ∀ y : D.what₂.LL, D.what₂.embLL y = (((Tp.psi w).val v)⁻¹ : ℂˣ).1 →
      nch.embW w y = algebraMap (nch.Oe w) (FractionRing (nch.Oe w)) (algebraMap (D.ntw.Ok (nch.twI w) (nch.k' w)) (nch.Oe w)
        ((nch.psi' w (D.ntw.art (nch.twI w) (nch.Q w) σ) : (D.ntw.Ok (nch.twI w) (nch.k' w))ˣ) : D.ntw.Ok (nch.twI w) (nch.k' w)))

theorem NGalChrTied.psiChoice {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} (T : NGalChrTied D C nch Tp)
    (h : NChTie D nch) (a : D.nd.Loc) (v : PlE D.host) (hQ : v ∉ nch.Q (D.nd.w a))
    (hl : v ∉ placesOver D.host.E (D.what₂.places.resChar (D.nd.w a)))
    (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (hB : IsPlaceOver (F := D.host.E) B v)
    (hσ : IsFrob (F := D.host.E) B (normV v) σ) (y : D.what₂.LL)
    (hy : D.what₂.embLL y = (((Tp.psi (D.nd.w a)).val v)⁻¹ : ℂˣ).1) :
    nch.embW (D.nd.w a) y = algebraMap (nch.Oe (D.nd.w a)) (FractionRing (nch.Oe (D.nd.w a)))
      (algebraMap (D.ntw.Ok (nch.twI (D.nd.w a)) (nch.k' (D.nd.w a))) (nch.Oe (D.nd.w a))
      ((nch.psi' (D.nd.w a) (D.ntw.art (nch.twI (D.nd.w a)) (nch.Q (D.nd.w a)) σ) :
        (D.ntw.Ok (nch.twI (D.nd.w a)) (nch.k' (D.nd.w a)))ˣ) : D.ntw.Ok (nch.twI (D.nd.w a)) (nch.k' (D.nd.w a)))) := by
  obtain ⟨ψ0, -, hW, hK⟩ := h.psi_eq
  have hU : (Tp.psi (D.nd.w a)).UnrAt v := by
    rw [(T.psi_is a).ram, h.Q_eq a]
    exact hQ
  have hl' : v ∉ placesOver D.host.E (D.nd.l a) := by
    rw [← D.nd.w_l a]
    exact hl
  have hg := T.psiL a v (Set.mem_univ v) hl' hU B σ hB hσ

  have hg' : D.what₂.embLL ((ψ0 (D.nd.w a) σ : (D.what₂.LL)ˣ) : D.what₂.LL) =
      (((Tp.psi (D.nd.w a)).val v)⁻¹ : ℂˣ).1 := by
    rw [← D.naut.iota_LL a, hK a σ]
    simpa [toC] using hg
  have hyy : y = ((ψ0 (D.nd.w a) σ : (D.what₂.LL)ˣ) : D.what₂.LL) :=
    D.what₂.embLL.injective (hy.trans hg'.symm)
  rw [hyy]
  exact hW (D.nd.w a) σ

structure CharacterChoiceData' (D : D7) (nch : NChoice D) where
  C : CharFrame D
  val : ValLL0 D C
  tp : TupTied D C nch
  dt : DtTied D C
  n : NCharTied D C nch tp
  gal : NGalChrTied D C nch tp
  psi' : PsiChoiceCompatible D C nch tp

theorem HChar.ValuesIn.qb {D : D7} (T : HostTied D) {χ : HChar D.host.E} {s : ℝ} (h : χ.ValuesIn s D.what₂.embLL)
    (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : χ.UnrAt v) : ∃ y : D.what₂.LL, T.fr.ι (T.jLL y) = χ.valTw s v := by
  obtain ⟨y, hy⟩ := h v hv
  exact ⟨y, by rw [T.embLL, hy]⟩

end Formalism.L2.Host
end
end

-- bundled from Formalism.LocalToGlobal.UnitaryNorms.CharRat
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem ide_fst_mul {L : Type} [Field L] [NumberField L] (a b : Ideles L) (w : InfinitePlace L) :
    ((a * b : Ideles L) : AdeleRing (𝓞 L) L).1 w = (a : AdeleRing (𝓞 L) L).1 w * (b : AdeleRing (𝓞 L) L).1 w := rfl

theorem infDiag_fst {L : Type} [Field L] [NumberField L] (k : Lˣ) (w : InfinitePlace L) :
    ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L).1 w = algebraMap L w.Completion (k : L) := by
  classical
  have h : ∀ s : Finset (InfinitePlace L),
      (((∏ w' ∈ s, (infIdele L w').comp (atInf w')) k : Ideles L) : AdeleRing (𝓞 L) L).1 w =
        if w ∈ s then algebraMap L w.Completion (k : L) else 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, MonoidHom.mul_apply, ide_fst_mul, ih]
      by_cases hwa : w = a
      · subst hwa
        rw [if_neg ha, mul_one, if_pos (Finset.mem_insert_self _ _)]
        exact infIdele_fst_self L w _
      · have h1 : (((infIdele L a).comp (atInf a)) k : AdeleRing (𝓞 L) L).1 w = 1 := infIdele_fst_ne L a w hwa _
        rw [h1, one_mul]
        simp [Finset.mem_insert, hwa]
  have := h Finset.univ
  rwa [if_pos (Finset.mem_univ _)] at this

theorem isFinIdele_diag {L : Type} [Field L] [NumberField L] (k : Lˣ) :
    IsFinIdele (diagUnits L k * (infDiag k)⁻¹) := by
  intro w
  have h1 : ((infDiag k * (infDiag k)⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 w = 1 := by
    rw [mul_inv_cancel]; rfl
  rw [ide_fst_mul, infDiag_fst] at h1
  rw [ide_fst_mul]
  exact h1

theorem DtTied.rat_val {D : D7} {C : CharFrame D} (T : DtTied D C) (χ : HChar D.host.E) (f : D.Dt →* ℂˣ)
    (hf : ∀ a : Ideles D.host.E, IsFinIdele a → f (T.eDt a) = χ.1 a) :
    letI := D.host.cmStar
    ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
      f (D.e1Dt z) = (χ.inf k)⁻¹ := by
  intro k z hz
  have h1 : T.eDt (infDiag k) = 1 := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, map_prod]
    exact Finset.prod_eq_one fun w _ => T.inf w _
  have h2 := hf _ (isFinIdele_diag k)
  rw [map_mul, map_inv, h1, inv_one, mul_one, T.rat k z hz, map_mul, map_inv, χ.2.2 k, one_mul] at h2
  exact h2

theorem DtTied.muTil_rat {D : D7} {C : CharFrame D} (T : DtTied D C) (j : Fin D.R.m) :
    letI := D.host.cmStar
    ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
      D.muTil (j.1 + 1) (D.e1Dt z) = ((C.mu0 j).inf k)⁻¹ :=
  T.rat_val (C.mu0 j) _ (T.muTil_eq j)

theorem DtTied.chiD_rat {D : D7} {C : CharFrame D} (T : DtTied D C) :
    letI := D.host.cmStar
    ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
      D.chiD (D.e1Dt z) = (C.chiPsi.inf k)⁻¹ :=
  T.rat_val C.chiPsi _ T.chiD_eq

theorem emb_conj {R : Ranks} (H : Formalism.BasicNotions.Host R) (g : R.GG) (x : H.E) :
    H.emb g (H.conj x) = starRingEnd ℂ (H.emb g x) := by
  exact H.conjE_apply (H.emb g) x

theorem IsChiPsi.rat {R : Ranks} {H : Formalism.BasicNotions.Host R} {χ : HChar H.E} (h : IsChiPsi H χ) (k : H.Eˣ) (z : H.E)
    (hz : z * H.conj (k : H.E) = k) : (((χ.inf k)⁻¹ : ℂˣ) : ℂ) = ∏ g : R.Psi, (H.emb (g : R.GG) z)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, h.inf k, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  congr 1
  have hx : H.emb (g : R.GG) (k : H.E) ≠ 0 := (map_ne_zero _).mpr k.ne_zero
  have h1 : H.emb (g : R.GG) z * starRingEnd ℂ (H.emb (g : R.GG) (k : H.E)) = H.emb (g : R.GG) (k : H.E) := by
    rw [← emb_conj, ← map_mul, hz]
  show (H.emb (g : R.GG) (k : H.E) / ((‖H.emb (g : R.GG) (k : H.E)‖ : ℝ) : ℂ)) ^ (2 : ℤ) = _
  set x := H.emb (g : R.GG) (k : H.E) with hxdef
  have hc : starRingEnd ℂ x ≠ 0 := (map_ne_zero _).mpr hx
  have h2 : ((‖x‖ : ℝ) : ℂ) ^ 2 = x * starRingEnd ℂ x := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have h3 : H.emb (g : R.GG) z = x / starRingEnd ℂ x := (eq_div_iff hc).mpr h1
  rw [zpow_ofNat, div_pow, h2, h3]
  field_simp

theorem hasInf_even_rat {R : Ranks} {H : Formalism.BasicNotions.Host R} {χ : HChar H.E} {m : R.Psi → ℤ}
    (h : χ.HasInf (embPsi H) (fun g => 2 * m g)) (k : H.Eˣ) (z : H.E) (hz : z * H.conj (k : H.E) = k) :
    ((χ.inf k : ℂˣ) : ℂ) = ∏ g : R.Psi, H.emb (g : R.GG) z ^ m g := by
  rw [h k]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hx : H.emb (g : R.GG) (k : H.E) ≠ 0 := (map_ne_zero _).mpr k.ne_zero
  have h1 : H.emb (g : R.GG) z * starRingEnd ℂ (H.emb (g : R.GG) (k : H.E)) = H.emb (g : R.GG) (k : H.E) := by
    rw [← emb_conj, ← map_mul, hz]
  show (H.emb (g : R.GG) (k : H.E) / ((‖H.emb (g : R.GG) (k : H.E)‖ : ℝ) : ℂ)) ^ (2 * m g) = _
  set x := H.emb (g : R.GG) (k : H.E) with hxdef
  have hc : starRingEnd ℂ x ≠ 0 := (map_ne_zero _).mpr hx
  have h2 : ((‖x‖ : ℝ) : ℂ) ^ 2 = x * starRingEnd ℂ x := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have h3 : H.emb (g : R.GG) z = x / starRingEnd ℂ x := (eq_div_iff hc).mpr h1
  rw [zpow_mul]
  congr 1
  rw [zpow_ofNat, div_pow, h2, h3]
  field_simp

theorem DtTied.muTil_rat' {D : D7} {C : CharFrame D} (T : DtTied D C) (j : Fin D.R.m) (m : D.R.Psi → ℤ)
    (hm : ∀ g, (m g : ℚ) = eExp D j g) :
    letI := D.host.cmStar
    ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
      ((D.muTil (j.1 + 1) (D.e1Dt z) : ℂˣ) : ℂ) = ∏ g : D.R.Psi, D.host.emb (g : D.R.GG) (z : D.host.E) ^ m g := by
  intro k z hz
  obtain ⟨n, hn, hinf⟩ := (C.isMu0 j).inf
  have e : n = fun g => 2 * (-m g) := funext fun g => by
    have h0 : (n g : ℚ) = 2 * -eExp D j g := hn g
    rw [← hm g] at h0
    exact_mod_cast h0
  subst e
  rw [T.muTil_rat j k z hz, Units.val_inv_eq_inv_val, hasInf_even_rat hinf k z hz, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun g _ => by rw [zpow_neg, inv_inv]

end Formalism.L2.Host
end
end

