import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEmbeddingIdealLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstEqInvChar
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.Datum
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.PinCoord

theorem mk_sum_smul {O La : Type} [CommRing O] [AddCommGroup La] [Module O La] (J : Submodule O La) {r : ℕ}
    (c : Fin r → O) (x : Fin r → La) : (Submodule.Quotient.mk (∑ b, c b • x b) : La ⧸ J) =
      ∑ b, c b • (Submodule.Quotient.mk (x b) : La ⧸ J) := by
  change J.mkQ _ = _
  rw [map_sum]
  rfl

theorem isUnit_det_of_span : ∀ {O La ι : Type} [CommRing O] [AddCommGroup La] [Module O La] (P : Finset ι) (k : ι → Type) [∀ i, CommRing (k i)] (φ : ∀ i, O → k i) {r : ℕ} (ρ : ∀ i, Fin r → La →+ k i), (∀ i a c x, ρ i a (c • x) = φ i c * ρ i a x) → ∀ (J : Submodule O La), (∀ x, x ∈ J → ∀ i ∈ P, ∀ a, ρ i a x = 0) → (∀ t : ∀ i, Fin r → k i, ∃ x, ∀ i ∈ P, ∀ a, ρ i a x = t i a) → ∀ x : Fin r → La, Submodule.span O (Set.range fun b => (Submodule.Quotient.mk (x b) : La ⧸ J)) = ⊤ → ∀ i ∈ P, IsUnit (Matrix.of fun b a => ρ i a (x b)).det := by
  intro O La ι _ _ _ P k _ φ r ρ hs J hJ hon x hx i hi
  classical
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_surjective_iff_isUnit]
  intro t
  obtain ⟨v, hv⟩ := hon (Pi.single i t)
  have hm : (Submodule.Quotient.mk v : La ⧸ J) ∈ Submodule.span O (Set.range fun b => (Submodule.Quotient.mk (x b) : La ⧸ J)) :=
    hx ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hm
  have hw : v - ∑ b, c b • x b ∈ J := by
    rw [← Submodule.Quotient.eq]
    rw [← hc]
    exact (mk_sum_smul J c x).symm
  refine ⟨fun b => φ i (c b), funext fun a => ?_⟩
  have h1 := hJ _ hw i hi a
  rw [map_sub, map_sum, sub_eq_zero] at h1
  simp only [hs] at h1
  have h2 := hv i hi a
  rw [Pi.single_eq_same] at h2
  rw [← h2, h1]
  simp [Matrix.vecMul, dotProduct]

theorem span_of_isUnit_det : ∀ {O La ι : Type} [CommRing O] [AddCommGroup La] [Module O La] (P : Finset ι) (k : ι → Type) [∀ i, CommRing (k i)] (φ : ∀ i, O → k i), (∀ t : ∀ i, k i, ∃ c, ∀ i ∈ P, φ i c = t i) → ∀ {r : ℕ} (ρ : ∀ i, Fin r → La →+ k i), (∀ i a c x, ρ i a (c • x) = φ i c * ρ i a x) → ∀ (J : Submodule O La), (∀ x, (∀ i ∈ P, ∀ a, ρ i a x = 0) → x ∈ J) → ∀ x : Fin r → La, (∀ i ∈ P, IsUnit (Matrix.of fun b a => ρ i a (x b)).det) → Submodule.span O (Set.range fun b => (Submodule.Quotient.mk (x b) : La ⧸ J)) = ⊤ := by
  intro O La ι _ _ _ P k _ φ hcrt r ρ hs J hJ x hu
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective J q
  have he : ∀ i, ∃ e : Fin r → k i, i ∈ P → Matrix.vecMul e (Matrix.of fun b a => ρ i a (x b)) = fun a => ρ i a v := by
    intro i
    by_cases hi : i ∈ P
    · have hs' := Matrix.vecMul_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hu i hi))
      obtain ⟨e, he⟩ := hs' (fun a => ρ i a v)
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose e he using he
  choose c hc using fun b : Fin r => hcrt fun i => e i b
  have hmem : v - ∑ b, c b • x b ∈ J := hJ _ fun i hi a => by
    rw [map_sub, map_sum, sub_eq_zero]
    simp only [hs, hc _ i hi]
    have := congrFun (he i hi) a
    rw [← this]
    simp [Matrix.vecMul, dotProduct]
  have e1 : (Submodule.Quotient.mk v : La ⧸ J) = ∑ b, c b • (Submodule.Quotient.mk (x b) : La ⧸ J) := by
    rw [(Submodule.Quotient.eq J).2 hmem]
    exact mk_sum_smul J c x
  rw [e1]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem adjoint_comp_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (kst : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d), (∀ u v : Dw.La, (d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) - Dw.EF u (cHalf H d.I • qRep (k (Submodule.Quotient.mk v)))) → ∀ f : Dw.La →ₗ[𝓞 E] Dw.La, (∀ x, (Submodule.Quotient.mk (f x) : LaI Xo c d) = k (Submodule.Quotient.mk x)) → (∀ x x', (d.pd : ℤ) ∣ Dw.EF (f x) (f x') - Dw.EF x x') → ∀ a : Dw.La, kst (Submodule.Quotient.mk (f a)) = (Submodule.Quotient.mk a : LaJ Xo c d) := by
  intro E _ _ _ H Dw l Xo c n d hd k kst hk f hf1 hf2 a
  obtain ⟨-, hM, -, hMb, hI, -⟩ := hd
  have hp := GlobalTheory.DatumInverseCharacter.half_prod hM hMb
  have hc := GlobalTheory.DatumInverseCharacter.cHalf_mem (H := H) d.I
  have hc1 := (GlobalTheory.HalfPairing.cHalf_spec (H := H) d.I hI).2
  have hN : d.pd ≠ 0 := by
    intro h
    have := d.l₂.three_le
    rw [hM, h] at this
    omega
  have hpd : (d.pd : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have : Ideal.span {(d.pd : 𝓞 E)} ≤ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := hp ▸ Ideal.mul_le_right
    exact this (Ideal.subset_span rfl)
  rw [← GlobalTheory.HalfPairing.qRep_mk (kst (Submodule.Quotient.mk (f a))), Submodule.Quotient.eq]
  set z := qRep (kst (Submodule.Quotient.mk (f a) : LaJ Xo c d)) with hz
  set t := cHalf H d.I with ht
  have hdiv : ∀ v, (d.pd : ℤ) ∣ Dw.EF (z - a) (t • v) := by
    intro v
    have h1 := hk (f a) v
    have h2 := GlobalTheory.DatumInverseCharacter.dvd_right Dw hp hc (f a)
      (w := qRep (k (Submodule.Quotient.mk v)) - f v) (by
        rw [← Submodule.Quotient.eq, GlobalTheory.HalfPairing.qRep_mk, hf1])
    have h3 := hf2 a (t • v)
    rw [map_smul] at h3
    rw [smul_sub, map_sub] at h2
    have := dvd_add (dvd_add h1 h2) h3
    rw [map_sub, LinearMap.sub_apply]
    rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
  have h4 : H.bar t • (z - a) ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) :=
    GlobalTheory.DatumInverseCharacter.mem_of_modN Dw hpd (GlobalTheory.DatumInverseCharacter.modN_of_dvd Dw (Nat.pos_of_ne_zero hN)
      fun q => by rw [Dw.adj, GlobalTheory.DatumInverseCharacter.bar_bar]; exact hdiv q)
  have h5 : (H.bar t - 1) • (z - a) ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) := by
    refine Submodule.smul_mem_smul ?_ trivial
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hc1
    rwa [map_sub, map_one] at this
  have := sub_mem h4 h5
  rwa [sub_smul, one_smul, sub_sub_cancel] at this

theorem topL_mul {κ : Type} [CommRing κ] {n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin n) (Fin r) κ) (B : Matrix (Fin r) (Fin r) κ) :
    topL r (A * B) = topL r A * B := by
  ext i j
  simp only [topL, Matrix.mul_apply, dif_pos (And.intro (lt_of_lt_of_le i.2 hrn) j.2), i.2, j.2, true_and,
    lt_of_lt_of_le i.2 hrn, Fin.is_lt, dite_true]

theorem topL_of {κ : Type} [Zero κ] {n r : ℕ} (hrn : r ≤ n) (A : Matrix (Fin n) (Fin r) κ) :
    topL r A = Matrix.of fun b a => A (Fin.castLE hrn b) a := by
  ext i j
  simp only [topL, dif_pos (And.intro (lt_of_lt_of_le i.2 hrn) j.2), Matrix.of_apply]
  rfl

theorem image_eq_range {α : Type} {n r : ℕ} (hrn : r ≤ n) (x : Fin n → α) :
    x '' {b | b.val < r} = Set.range fun a : Fin r => x (Fin.castLE hrn a) := by
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b.val, hb⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, a.2, rfl⟩

theorem exists_const_eq_inv_char : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (xJ : Fin n → LaJ Xo c d), d.PhiPin ph ψ xJ → ∀ (r : ℕ), Dw.p + Dw.q = r → r ≤ n → ∀ (Q : Finset (Pl E)) (ξ : ∀ P : Pl E, (kP P)ˣ →* ℂˣ) (ρ : ∀ P : Pl E, Fin r → Dw.La →+ kP P), (∀ (P : Pl E) (a : Fin r) (t : 𝓞 E) (x : Dw.La), ρ P a (t • x) = Ideal.Quotient.mk P.asIdeal (H.bar t) * ρ P a x) → (∀ x : Dw.La, x ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) ↔ ∀ P ∈ Q, ∀ a, ρ P a x = 0) → (∀ t : ∀ P : Pl E, Fin r → kP P, ∃ x, ∀ P ∈ Q, ∀ a, ρ P a x = t P a) → (∀ k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d, ∃ (f : Dw.La →ₗ[𝓞 E] Dw.La) (y : ∀ P : Pl E, GL (Fin r) (kP P)), (∀ x, (Submodule.Quotient.mk (f x) : LaI Xo c d) = k (Submodule.Quotient.mk x)) ∧ (∀ x x', (d.pd : ℤ) ∣ Dw.EF (f x) (f x') - Dw.EF x x') ∧ (∀ P ∈ Q, ∀ x : Fin n → Dw.La, (Matrix.of fun b a => ρ P a (x b)) = (Matrix.of fun b a => ρ P a (f (x b))) * (y P).val) ∧ (((ψ k : c.Fˣ) : c.F) : ℂ) = ∏ P ∈ Q, ((ξ P (Matrix.GeneralLinearGroup.det (y P)) : ℂˣ) : ℂ)) → ∃ u : ∀ P : Pl E, (kP P)ˣ, ∀ x : Fin n → Dw.La, (if h : ∀ P ∈ Q, IsUnit (topL r (Matrix.of fun b a => ρ P a (x b))).det then ∏ P ∈ Q.attach, (((ξ P.1 (h P.1 P.2).unit)⁻¹ : ℂˣ) : ℂ) else 0) = (∏ P ∈ Q, (((ξ P (u P))⁻¹ : ℂˣ) : ℂ)) * ((ph (fun b => Submodule.Quotient.mk (x b)) : c.F) : ℂ) := by
  intro E _ _ _ H Dw l Xo c n d hd ph ψ xJ hpin r hr hrn Q ξ ρ hs hker hon hfy
  subst hr
  obtain ⟨hc1, hc2, hc3, hc4, hc5, -⟩ := hpin
  obtain ⟨-, huniq, adj, -, hadj⟩ := GlobalTheory.HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
  have hcrt : ∀ t : ∀ P : Pl E, kP P, ∃ c, ∀ P ∈ Q, Ideal.Quotient.mk P.asIdeal (H.bar c) = t P := fun t => by
    obtain ⟨c, hc⟩ := GlobalTheory.BasePoint.crt_places Q t
    exact ⟨H.bar.symm c, fun P hP => by rw [RingEquiv.apply_symm_apply]; exact hc P hP⟩

  have hspan : ∀ x : Fin n → Dw.La, Submodule.span (𝓞 E) ((fun b => (Submodule.Quotient.mk (x b) : LaJ Xo c d)) ''
      {b | b.val < Dw.p + Dw.q}) = ⊤ ↔ ∀ P ∈ Q, IsUnit (topL (Dw.p + Dw.q) (Matrix.of fun b a => ρ P a (x b))).det := by
    intro x
    rw [image_eq_range hrn]
    simp only [topL_of hrn, Matrix.of_apply]
    exact ⟨isUnit_det_of_span Q (fun P => kP P) (fun P c => Ideal.Quotient.mk P.asIdeal (H.bar c)) ρ hs _
        (fun y hy => (hker y).1 hy) hon (fun a => x (Fin.castLE hrn a)),
      span_of_isUnit_det Q (fun P => kP P) (fun P c => Ideal.Quotient.mk P.asIdeal (H.bar c)) hcrt ρ hs _
        (fun y hy => (hker y).2 hy) (fun a => x (Fin.castLE hrn a))⟩
  set X₀ : Fin n → Dw.La := fun b => qRep (xJ b) with hX₀
  have hX₀mk : (fun b => (Submodule.Quotient.mk (X₀ b) : LaJ Xo c d)) = xJ :=
    funext fun b => GlobalTheory.HalfPairing.qRep_mk (xJ b)
  have hX₀u := (hspan X₀).1 (by rw [hX₀mk]; exact hc5)
  let u : ∀ P : Pl E, (kP P)ˣ := fun P =>
    if h : IsUnit (topL (Dw.p + Dw.q) (Matrix.of fun b a => ρ P a (X₀ b))).det then h.unit else 1
  have hu : ∀ P ∈ Q, ((u P : (kP P)ˣ) : kP P) = (topL (Dw.p + Dw.q) (Matrix.of fun b a => ρ P a (X₀ b))).det :=
    fun P hP => by simp only [u, dif_pos (hX₀u P hP), IsUnit.unit_spec]
  refine ⟨u, fun x => ?_⟩
  split_ifs with h
  ·
    have hxs := (hspan x).2 h
    rw [image_eq_range hrn] at hxs
    have hJs : Submodule.span (𝓞 E) (Set.range fun a : Fin (Dw.p + Dw.q) => xJ (Fin.castLE hrn a)) = ⊤ := by
      rw [← image_eq_range hrn]; exact hc5
    obtain ⟨kst, hkst, -⟩ := huniq _ _ hJs hxs
    have hk := (hadj (adj kst) kst).2 rfl
    have hph : ph (fun b => Submodule.Quotient.mk (x b)) = (((ψ (adj kst))⁻¹ : c.Fˣ) : c.F) := by
      have e1 : ph (fun b => Submodule.Quotient.mk (x b)) = ph (fun b => kst (xJ b)) :=
        hc1 _ _ fun b hb => (hkst ⟨b.val, hb⟩).symm
      rw [e1, hc3 (adj kst) kst hk xJ, hc4, mul_one]
    obtain ⟨f, y, hf1, hf2, hf3, hf4⟩ := hfy (adj kst)
    have hC := adjoint_comp_isometry E H Dw l Xo c n d hd (adj kst) kst hk f hf1 hf2
    have hfx : ∀ b : Fin n, b.val < Dw.p + Dw.q → ∀ P ∈ Q, ∀ a, ρ P a (f (x b)) = ρ P a (X₀ b) := by
      intro b hb P hP a
      have e2 : (Submodule.Quotient.mk (f (x b)) : LaJ Xo c d) = Submodule.Quotient.mk (X₀ b) := by
        apply kst.injective
        rw [hC, congrFun hX₀mk b]
        exact (hkst ⟨b.val, hb⟩).symm
      have := (hker (f (x b) - X₀ b)).1 ((Submodule.Quotient.eq _).1 e2) P hP a
      rwa [map_sub, sub_eq_zero] at this
    have hunit : ∀ (P : Pl E) (hP : P ∈ Q), (h P hP).unit = u P * Matrix.GeneralLinearGroup.det (y P) := by
      intro P hP
      apply Units.ext
      rw [IsUnit.unit_spec, Units.val_mul, hu P hP, Matrix.GeneralLinearGroup.val_det_apply, hf3 P hP x,
        topL_mul hrn, Matrix.det_mul]
      congr 2
      rw [topL_of hrn, topL_of hrn]
      ext b a
      exact hfx _ (by simp) P hP a
    have hL : ∏ P ∈ Q.attach, (((ξ P.1 (h P.1 P.2).unit)⁻¹ : ℂˣ) : ℂ) =
        (∏ P ∈ Q, (((ξ P (u P))⁻¹ : ℂˣ) : ℂ)) * (∏ P ∈ Q, ((ξ P (Matrix.GeneralLinearGroup.det (y P)) : ℂˣ) : ℂ))⁻¹ := by
      calc ∏ P ∈ Q.attach, (((ξ P.1 (h P.1 P.2).unit)⁻¹ : ℂˣ) : ℂ)
          = ∏ P ∈ Q.attach, ((((ξ P.1 (u P.1))⁻¹ : ℂˣ) : ℂ) *
              (((ξ P.1 (Matrix.GeneralLinearGroup.det (y P.1)) : ℂˣ) : ℂ))⁻¹) :=
            Finset.prod_congr rfl fun P _ => by
              rw [hunit P.1 P.2, map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val (ξ P.1 (Matrix.GeneralLinearGroup.det (y P.1)))]
        _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
            Finset.prod_attach Q (fun P => (((ξ P (u P))⁻¹ : ℂˣ) : ℂ)),
            Finset.prod_attach Q (fun P => ((ξ P (Matrix.GeneralLinearGroup.det (y P)) : ℂˣ) : ℂ))]
    rw [hL, ← hf4, hph, Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
  ·
    have h0 : ph (fun b => Submodule.Quotient.mk (x b)) = 0 := by
      by_contra hne
      exact h ((hspan x).1 (hc2 _ hne))
    rw [h0]
    simp

end GlobalTheory.PinCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelBlocksUnitaryFrame
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKFrameModel

theorem exists_frame_model : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∃ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ),
      M₁.IsGood B.ψ ∧ IsFrameCo σ X.J W.J x y M₁.co blk ∧ IsEv B M M₁ 1 1 ∅ e ∧ c ≠ 0 ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c * thetaSum F Φ := by
  have hA1 := @GlobalTheory.T.symplectic_basis_of_unitary_frame
  have hA2 := @GlobalTheory.T.symplectic_block_basis_orthogonal

  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair q x y hxy
  have hB := hpair.base
  have hX := hpair.herm
  have hW := hpair.skew
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hXd : X.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hX.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hWd : W.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hW.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det W.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  obtain ⟨b, blk, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    hA1 σ X.J W.J x y hσ hB.cm.2.2.1 hX.herm hXd hW.skew hWd hxy
  obtain ⟨co, hco, hfr⟩ := hA2 σ X.J W.J x y b blk h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨e, ei, ev, hei, hmaps, hheis, hSB, hvac, hstd, hpure, hbij⟩ :=
    GlobalTheory.T.darboux_coords_good_model F E σ B n d X W M r s r' s' hpair.base hpair.herm hpair.skew hpair.good co hco
  let M₁ : Model σ X W := ⟨co, fun v => ev v (M.vac v), M.μ, M.dom⟩
  have hM₁ : M₁.IsGood B.ψ := ⟨hco, hvac, hstd, hpair.good.haar, hpair.good.dom⟩
  have hne : ∃ f : SInf F (Fin n × Fin d), f ≠ 0 := by
    by_contra hall
    push_neg at hall
    obtain ⟨φ, hφ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
    have hle : schA F (Fin n × Fin d) ≤ ⊥ := by
      refine Submodule.span_le.2 ?_
      rintro Φ ⟨f, g, -, rfl⟩
      rw [hall f]
      show pureA F 0 g = 0
      funext x
      simp [pureA]
    have h0 : φ = 0 := (Submodule.mem_bot ℂ).1 (hle hφ)
    exact hθ (by rw [h0]; simp [thetaSum])
  have hev : IsEv B M M₁ 1 1 ∅ e := by
    refine ⟨hmaps, fun z Φ hΦ => ?_, fun u hu => hu.elim, ei, ev, ?_, fun v => ⟨rfl, hSB v⟩, hpure⟩
    · have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
      exact hheis z Φ hΦ
    · obtain ⟨f, hf⟩ := hne
      obtain ⟨g, rfl⟩ := hei f
      intro h
      exact hf (by rw [h]; rfl)
  obtain ⟨c₀, hc₀, hth⟩ := GlobalTheory.T.weil_eigen_schwartz_surjective F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  exact ⟨M₁, blk, e, c₀, hM₁, hfr, hev, hc₀, hth⟩

end GlobalTheory.ThKFrameModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataOverRowFieldConditionsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedTupleData_over_rowField_conditions : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  first | exact @GlobalTheory.PinsOverClauses.pinsOverL_of_clauses | exact GlobalTheory.PinsOverClauses.pinsOverL_of_clauses | (intros; apply GlobalTheory.PinsOverClauses.pinsOverL_of_clauses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIntegralCompletedHomLattice
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CosetOrth.LatInt

theorem exists_pow_mem (D : D7) : ∃ k : ℕ, (((D.host.QS * D.host.q) ^ k : ℕ) : 𝓞 D.host.E) ∈ D.host.𝔟 := by
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∈ D.host.𝔟.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hJ, hp⟩
    have hne : J ≠ ⊥ := fun e => hb (le_bot_iff.1 (e ▸ hJ))
    exact GlobalTheory.HalfCompare.two_q_mem (P := ⟨J, hp, hne⟩) (Ideal.dvd_iff_le.2 hJ)
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [Nat.cast_pow]; exact hk⟩

theorem homL_entry {D : D7} {N N' : ℕ} {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    A i j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    have h1 : (Pi.single j (1 : D.host.E) : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
      intro l _
      by_cases h : l = j
      · subst h
        rw [Pi.single_eq_same]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _
    have h2 := hA _ h1 i trivial
    rw [Matrix.mulVec_single_one] at h2
    exact h2
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem YYl_entry {D : D7} {N N' : ℕ} {B : Matrix (Fin N') (Fin N) D.host.E}
    (hB : B ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    B i j ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (homL_entry hA i j)
    have : (a • A) i j = c • a := by
      rw [Matrix.smul_apply, smul_eq_mul, ← hc, Algebra.smul_def, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ c ha
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem mul_int {D : D7} {n : 𝓞 D.host.E} (hn : n ∈ D.host.𝔟) {x : D.host.E}
    (hx : x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = algebraMap (𝓞 D.host.E) D.host.E n * x := by
  have hb := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D
  have h1 : algebraMap (𝓞 D.host.E) D.host.E n * x ∈
      (D.host.𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0 :=
    FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hn) hx
  rw [Formalism.BasicNotions.Host.AA0, mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.2 hb)] at h1
  exact (FractionalIdeal.mem_one_iff _).1 h1

theorem inHat_tmul {D : D7} {α : Af D.host.F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F) (c x : D.host.E) (b : 𝓞 D.host.E)
    (hb : algebraMap (𝓞 D.host.E) D.host.E b = c * x) :
    InHat 1 (algebraMap D.host.E (FA D) c * fe D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x)) := by
  have e : fe D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) =
      GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E α * algebraMap D.host.E (FA D) x := rfl
  rw [e, mul_left_comm, ← map_mul, ← hb]
  refine InHat.mul_left ((inHat_one_iff _).2 fun w => ?_) ((inHat_one_iff _).2 fun w => ?_)
  · exact GlobalTheory.AdeleBaseChange.adMap_int (F := D.host.F) (E := D.host.E) hα w
  · change Valued.v ((algebraMap (𝓞 D.host.E) D.host.E b : D.host.E) : w.adicCompletion D.host.E) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact w.valuation_le_one b

theorem exists_hatPt_of_mem_latO : ∀ {D : D7} (S T : HSp D) (r : D.host.E) (LB : Lat T), r ≠ 0 →
  (∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E, finPt (S := S) (T := T) rfl rfl r z ∈ (latO S T (stdLat S) LB fun _ => True) →
    z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank)) →
  ∃ k : ℕ, ∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) 1 u := by
  intro D S T r LB hr hz
  obtain ⟨k, hk⟩ := exists_pow_mem D
  refine ⟨k, fun u hu => ⟨Matrix.ext fun i j => GlobalTheory.LatVac.infPart_of_mem hu i j, fun i j => ?_⟩⟩
  refine GlobalTheory.LatVac.latO_induction (p := fun u => InHat 1
    (algebraMap D.host.E (FA D) ((((D.host.QS * D.host.q) ^ k : ℕ) : D.host.E) * r) * fe D (u i j))) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    have h1 := GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) hM
    have e : finPt (S := S) (T := T) rfl rfl r (-r • M) = GlobalTheory.LatVac.finTens 1 M := by
      have : (Matrix.of fun i j => -(r⁻¹ * (-r • M) (Fin.cast rfl i) (Fin.cast rfl j))) = M := by
        ext i j
        simp [hr]
      unfold finPt
      rw [this]
      rfl
    obtain ⟨b, hb⟩ := mul_int hk (YYl_entry (hz _ (e ▸ h1)) i j)
    refine inHat_tmul hα _ _ (-b) ?_
    rw [map_neg, hb, map_natCast, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [Matrix.zero_apply, map_zero, mul_zero]
    exact inHat_zero _
  · intro x y hx hy
    rw [Matrix.add_apply, map_add, mul_add]
    exact hx.add hy
  · intro x hx
    rw [Matrix.neg_apply, map_neg, mul_neg]
    exact hx.neg

end GlobalTheory.CosetOrth.LatInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceConjHeisenbergInvariantForm
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitInvFormF

theorem exists_invForm_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
            ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ ℓ f ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  obtain ⟨φ, hφ, hφ0, hd⟩ := GlobalTheory.T.splitPlace_thetaFunction_vacuum_conjugatePlace F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  obtain ⟨ℓ, h1, h2⟩ := GlobalTheory.HalfCoinv.exists_form (Y := conjHalf σ e nS nT) (ρ := heisL σ JS JT ξ₀ B.ψ)
    (B := commF σ JS JT ξ₀ B.ψ) (Θ := {g | IsThetaFunOF σ JS JT ξ₀ B.ψ g})
    (fun x hx x' hx' f => by
      show heisOF σ JS JT ξ₀ B.ψ x (heisOF σ JS JT ξ₀ B.ψ x' f) = heisOF σ JS JT ξ₀ B.ψ (x + x') f
      rw [heisOF_heisOF, symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun f => heisOF_zero f) (fun u y f => heisOF_comm u y f)
    (fun u hu g hg => exists_nsmul_fix he hu hg) hφ0 hd
  exact ⟨ℓ, fun u hu f hf => h1 u hu f hf, φ, hφ, h2⟩

end GlobalTheory.SplitInvFormF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDoublingPairDataIdentityCartanStatement
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaDoublingPairData_identity_cartan : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X → 1 ≤ P.a → P.a < P.d →
  ∃ (cA : GlobalTheory.Mem.Th.CptF X.A) (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)),
    GlobalTheory.Core.Rk.IP.Pair X.ψ X.θ X.A X.B X.χA X.χB (fun _ => 1) (fun _ => 1) (P.d - P.a) cA a X.om ν 𝓕 := by
  first | exact @GlobalTheory.NormRatio.exists_ipPair_one | exact GlobalTheory.NormRatio.exists_ipPair_one | (intros; apply GlobalTheory.NormRatio.exists_ipPair_one <;> assumption)
end

