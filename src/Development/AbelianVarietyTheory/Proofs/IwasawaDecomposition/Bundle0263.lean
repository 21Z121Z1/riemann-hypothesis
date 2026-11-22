import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGLocIdGChiTied
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TypePrimes

theorem nonempty_equiv_zmod (k : Type) [Ring k] {p : ℕ} (hp : p.Prime) (h : Nat.card k = p) : Nonempty (ZMod p ≃+* k) := by
  have : Finite k := Nat.finite_of_card_ne_zero (h ▸ hp.ne_zero)
  have := Fintype.ofFinite k
  exact ⟨ZMod.ringEquivOfPrime k hp (by rw [← Nat.card_eq_fintype_card, h])⟩

noncomputable def transport {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') (χ : MulChar k' ℂ) : MulChar k ℂ where
  toMonoidHom := χ.toMonoidHom.comp (e : k →* k')
  map_nonunit' a ha := χ.map_nonunit fun h => ha (by simpa using h.map e.symm)

theorem transport_apply {k k' : Type} [CommRing k] [CommRing k'] (e : k ≃+* k') (χ : MulChar k' ℂ) (a : k) :
    transport e χ a = χ (e a) := rfl

theorem orderOf_ofUnitHom {p : ℕ} (hp : p.Prime) (om : (ZMod p)ˣ →* ℂˣ) (h : Function.Injective om) :
    orderOf (MulChar.ofUnitHom om) = p - 1 := by
  have := Fact.mk hp
  have key : ∀ n : ℕ, MulChar.ofUnitHom om ^ n = 1 ↔ p - 1 ∣ n := by
    intro n
    rw [← ZMod.card_units p, ← Nat.card_eq_fintype_card, ← IsCyclic.exponent_eq_card,
      Monoid.exponent_dvd_iff_forall_pow_eq_one, MulChar.ext_iff]
    refine forall_congr' fun a => ?_
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, MulChar.ofUnitHom_coe, ← Units.val_pow_eq_pow_val, Units.val_eq_one,
      ← map_pow, map_eq_one_iff om h]
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((key _).2 dvd_rfl)) ((key _).1 (pow_orderOf_eq_one _))

section Orient

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem exists_oriented (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E) (p : ℕ) (hv : (p : 𝓞 F) ∈ v.asIdeal)
    (hx : x * σ x = (p : E)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (h1 : ∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x))
    (h2 : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F,
      (∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) ∧ (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
      Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 < 1 := by
  by_cases h : Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 < 1
  · exact ⟨sp, h1, h2, h⟩
  refine ⟨sp.trans RingEquiv.prodComm, fun y => ?_, fun a => ?_, ?_⟩
  · rw [RingEquiv.trans_apply, h1]; rfl
  · rw [RingEquiv.trans_apply, h2]; rfl
  have e1 : (sp (inclE (F := F) (v.adicCompletion F) (σ x))).2 = (sp (inclE (F := F) (v.adicCompletion F) x)).1 :=
    congrArg Prod.snd (h1 (inclE (F := F) (v.adicCompletion F) x))
  have e2 : (sp (inclE (F := F) (v.adicCompletion F) x)).1 * (sp (inclE (F := F) (v.adicCompletion F) (σ x))).1 =
      (p : v.adicCompletion F) := by
    rw [← Prod.fst_mul, ← map_mul, ← map_mul, hx, map_natCast, map_natCast, Prod.fst_natCast]
  have e3 : Valued.v (p : v.adicCompletion F) < 1 := by
    have : (p : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) := by simp
    rw [this, Examples₂.adicCompl_val_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v _).2 hv
  show Valued.v (sp (inclE (F := F) (v.adicCompletion F) (σ x))).2 < 1
  rw [e1]
  by_contra h'
  rw [← e2, map_mul] at e3
  exact absurd e3 (not_lt.2 (one_le_mul (not_lt.1 h') (not_lt.1 h)))

end Orient

section Generic

variable {X : Fields} {Pr : Primes X} {m : ℕ}

theorem g_mem_of_vG (hPr : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
  rw [← hPr.vG_norm i w hw]
  exact Ideal.absNorm_mem _

theorem mem_vG_of_g_mem (hPr : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs)
    (h : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal) : w ∈ Pr.vG i := by
  classical
  have h1 : ∃ j, w ∈ Pr.vG j := by
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h0 | h0 <;> exact ⟨_, h0⟩
  obtain ⟨j, hj⟩ := h1
  by_cases e : j = i
  · exact e ▸ hj
  exfalso
  have hne : Pr.g j ≠ Pr.g i := by
    have := hPr.g_ne
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hc : IsCoprime ((Pr.g j : ℕ) : 𝓞 X.E) ((Pr.g i : ℕ) : 𝓞 X.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (hPr.g_prime j) (hPr.g_prime i)).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact add_mem (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr hj)) (Ideal.mul_mem_left _ _ h)

theorem mem_vGs {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) : w ∈ Pr.vGs := by
  classical
  unfold Primes.vGs
  fin_cases i
  · exact Finset.mem_union.2 (Or.inl hw)
  · exact Finset.mem_union.2 (Or.inr hw)

theorem exists_gLoc (Ch : Chars X Pr m) (hf : 0 < X.f) (hPr : Pr.Ok) (hCh : Ch.Ok) (cm : CMData X.F X.E) (σ₀ : X.K →+* ℂ)
    (hs : ∀ i, GlobalTheory.St.G.SplitsIn X.E (Pr.g i)) :
    ∃ G : GLoc X.F X.E cm.sig Pr.g, G.piG = Pr.piG ∧
      (∀ j v h (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → ∀ n : ℕ,
        G.psi0 j v h (n : kv X.F v) = σ₀ (Ch.psi0 w (n : 𝓞 X.E ⧸ w.1.asIdeal))) ∧
      (∀ j v h (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → ∀ (s : Fin m) (n : ℕ)
        (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), (c : 𝓞 X.E ⧸ w.1.asIdeal) = n →
        G.chiB j v h s.1 (n : kv X.F v) = σ₀ ((Ch.chi s w c : X.Kˣ) : X.K)) ∧ CharacterCompatible G m := by
  classical
  have hnorm : ∀ i, (Pr.piG i : X.E) * cm.sig (Pr.piG i : X.E) = (Pr.g i : X.E) := fun i => by
    have := congrArg (algebraMap (𝓞 X.E) X.E) (hPr.piG_norm i)
    simp only [map_mul, map_natCast] at this
    exact this
  have hsp := fun i => (GlobalTheory.St.G.SplitPrime.split_place X.F X.E cm (Pr.g i) (hPr.g_prime i) (hs i)).2
  have hor := fun i v h => exists_oriented cm.sig v (Pr.piG i : X.E) (Pr.g i) h (hnorm i) _ (hsp i v h).2.2.choose_spec.1
    (hsp i v h).2.2.choose_spec.2
  choose sp sp1 sp2 sp3 using hor
  have ev := fun i v h => (nonempty_equiv_zmod (kv X.F v) (hPr.g_prime i) (hsp i v h).1).some
  have hw0 : ∀ i, ∃ w, w ∈ Pr.vG i := fun i => Finset.card_pos.1 (by rw [hPr.vG_card i]; exact hf)
  choose w0 hw0 using hw0
  have ew := fun i w (hw : w ∈ Pr.vG i) => (nonempty_equiv_zmod (𝓞 X.E ⧸ w.asIdeal) (hPr.g_prime i) (by
    rw [← hPr.vG_norm i w hw, Ideal.absNorm_apply, Submodule.cardQuot_apply])).some
  choose om omi hom using hCh.chi_om
  let om' : ∀ i, MulChar (ZMod (Pr.g i)) ℂ := fun i => MulChar.ofUnitHom ((Units.map (σ₀ : X.K →* ℂ)).comp (om i))
  have hin : ∀ {j v} (h : ((Pr.g j : ℕ) : 𝓞 X.F) ∈ v.asIdeal) (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → w.1 ∈ Pr.vG j := by
    rintro j v h w rfl
    refine mem_vG_of_g_mem hPr w.2 ?_
    have h' : algebraMap (𝓞 X.F) (𝓞 X.E) (Pr.g j : ℕ) ∈ w.1.asIdeal := h
    rwa [map_natCast] at h'

  have hval : ∀ j (w : {w // w ∈ Pr.vGs}) (hw : w.1 ∈ Pr.vG j) (s : Fin m) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ),
      (om' j ^ (2 * (s.1 + 1))) ((ew j w.1 hw).symm c) = σ₀ ((Ch.chi s w c : X.Kˣ) : X.K) := by
    intro j w hw s c
    have := Fact.mk (hPr.g_prime j)
    let a : (ZMod (Pr.g j))ˣ := Units.map ((ew j w.1 hw).symm : _ →* _) c
    have ha : (ew j w.1 hw).symm c = (a : ZMod (Pr.g j)) := rfl
    have hc : (c : 𝓞 X.E ⧸ w.1.asIdeal) = (((a : ZMod (Pr.g j)).val : ℕ) : 𝓞 X.E ⧸ w.1.asIdeal) := by
      rw [← map_natCast (ew j w.1 hw), ZMod.natCast_zmod_val, ← ha, RingEquiv.apply_symm_apply]
    rw [hom j w hw s a c hc, ha, MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, Units.val_pow_eq_pow_val, map_pow]
    rfl
  refine ⟨{ sp := sp, sp_sig := sp1, sp_alg := sp2, piG := Pr.piG, piG_norm := hnorm, sp_pi := sp3
            psi0 := fun i v h => ((σ₀ : X.K →* ℂ).compAddChar (Ch.psi0 ⟨w0 i, mem_vGs (hw0 i)⟩)).compAddMonoidHom
              (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).toRingHom.toAddMonoidHom)
            psi_zero_nontrivial_character := ?_
            chiB := fun i v h a => transport (ev i v h).symm (om' i ^ (2 * (a + 1))) }, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i v h h1
    apply hCh.psi_zero_nontrivial_character ⟨w0 i, mem_vGs (hw0 i)⟩
    ext x
    have h2 := DFunLike.congr_fun h1 (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).symm x)
    have h3 : σ₀ (Ch.psi0 ⟨w0 i, mem_vGs (hw0 i)⟩ (((ev i v h).symm.trans (ew i (w0 i) (hw0 i)))
      (((ev i v h).symm.trans (ew i (w0 i) (hw0 i))).symm x))) = 1 := h2
    rw [RingEquiv.apply_symm_apply, map_eq_one_iff σ₀ σ₀.injective] at h3
    exact h3
  · intro j v h w hw n
    show σ₀ (Ch.psi0 ⟨w0 j, mem_vGs (hw0 j)⟩ (((ev j v h).symm.trans (ew j (w0 j) (hw0 j))) (n : kv X.F v))) = _
    rw [map_natCast]
    have := hCh.characterAgreesOnPlaces j ⟨w0 j, mem_vGs (hw0 j)⟩ w (hw0 j) (hin h w hw) (n : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at this
    rw [this]
  · intro j v h w hw s n c hc
    show transport (ev j v h).symm (om' j ^ (2 * (s.1 + 1))) (n : kv X.F v) = _
    rw [transport_apply, map_natCast, ← hval j w (hin h w hw) s c, hc,
      map_natCast (ew j w.1 (hin h w hw)).symm]
  · intro i v h a b ha hb hab
    have h1 : om' i ^ (2 * (a + 1)) = om' i ^ (2 * (b + 1)) := by
      refine MulChar.ext' fun x => ?_
      have h2 : transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (ev i v h x) =
        transport (ev i v h).symm (om' i ^ (2 * (b + 1))) (ev i v h x) := DFunLike.congr_fun hab _
      rwa [transport_apply, transport_apply, RingEquiv.symm_apply_apply] at h2
    have h3 : (⟨a, ha⟩ : Fin m) = ⟨b, hb⟩ := by
      apply hCh.chi_inj ⟨w0 i, mem_vGs (hw0 i)⟩
      refine MonoidHom.ext fun c => Units.ext (σ₀.injective ?_)
      rw [← hval i ⟨w0 i, mem_vGs (hw0 i)⟩ (hw0 i) ⟨a, ha⟩ c, ← hval i ⟨w0 i, mem_vGs (hw0 i)⟩ (hw0 i) ⟨b, hb⟩ c, h1]
    exact congrArg Fin.val h3
  · intro i v h v' h' a n _
    show transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (n : kv X.F v) =
      transport (ev i v' h').symm (om' i ^ (2 * (a + 1))) (n : kv X.F v')
    rw [transport_apply, transport_apply, map_intCast (ev i v h).symm, map_intCast (ev i v' h').symm]
  · intro i
    refine ⟨om' i, orderOf_ofUnitHom (hPr.g_prime i) _ ((Units.map_injective σ₀.injective).comp (omi i)), ?_⟩
    intro v h a n _
    show transport (ev i v h).symm (om' i ^ (2 * (a + 1))) (n : kv X.F v) = _
    rw [transport_apply, map_intCast]

end Generic

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem exists_gLoc_idG_chiTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X →
    ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∃ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g),
      I.IdG l Z G ∧ CharacterCompatible G B.R.m := by
  intro B X I hI _ l Z
  have hf : 0 < B.fields.f := by
    unfold Fields.f
    rw [Fintype.card_pos_iff]
    by_contra h
    have h1 := B.fields_f
    unfold Fields.f at h1
    rw [not_nonempty_iff] at h
    rw [Fintype.card_eq_zero] at h1
    unfold Ranks.f Ranks.n at h1
    have := B.R.ord_pos
    omega
  obtain ⟨G, h1, h2, h3, h4⟩ := exists_gLoc I.Ch hf l.pr hI.ch_ok B.sp.cm B.embLL (I.rec7 l Z).nd.g_split
  exact ⟨G, ⟨h1, h2, h3⟩, h4⟩

end GlobalTheory.Mem.TypePrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjectiveBundleOfLatticeIsProjOver
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

section Generic

variable {Ω : Type} [Field Ω] {J : Type} [Fintype J] [DecidableEq J]

def genPoly (Ω : Type) [Field Ω] (j₀ j : J) : MvPolynomial {j // j ≠ j₀} Ω :=
  if h : j = j₀ then 1 else MvPolynomial.X ⟨j, h⟩

def genPt (Ω : Type) [Field Ω] (j₀ j : J) : FractionRing (MvPolynomial {j // j ≠ j₀} Ω) :=
  algebraMap _ _ (genPoly Ω j₀ j)

omit [Fintype J] in
theorem genPt_self (j₀ : J) : genPt Ω j₀ j₀ = 1 := by simp [genPt, genPoly]

omit [Fintype J] in

theorem eq_top_of_genPt_mem (j₀ : J) (K : Subfield (FractionRing (MvPolynomial {j // j ≠ j₀} Ω)))
    (h1 : ∀ a : Ω, algebraMap Ω _ a ∈ K) (h2 : ∀ j, genPt Ω j₀ j ∈ K) : K = ⊤ := by
  have h : ∀ p : MvPolynomial {j // j ≠ j₀} Ω, algebraMap _ _ p ∈ K := fun p => by
    induction p using MvPolynomial.induction_on with
    | C a => exact h1 a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      simpa [genPt, genPoly, j.2] using h2 j.1
  refine top_unique fun x _ => ?_
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial {j // j ≠ j₀} Ω) x
  exact div_mem (h p) (h q)

theorem eq_zero_of_sum_genPt (j₀ : J) (b : J → Ω) (h : ∑ j, algebraMap Ω _ (b j) * genPt Ω j₀ j = 0) : b = 0 := by
  have h' : ∑ j, MvPolynomial.C (b j) * genPoly Ω j₀ j = 0 := by
    apply IsFractionRing.injective _ (FractionRing (MvPolynomial {j // j ≠ j₀} Ω))
    rw [map_zero, map_sum, ← h]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; rfl
  have e : ∀ x : J → Ω, x j₀ = 1 → ∑ j, b j * x j = 0 := fun x hx => by
    have := congrArg (MvPolynomial.eval fun j : {j // j ≠ j₀} => x j.1) h'
    rw [map_zero, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀
    · subst hj; simp [genPoly, hx]
    · simp [genPoly, hj]
  have h0 : b j₀ = 0 := by simpa [Pi.single_apply] using e (Pi.single j₀ 1) (by simp)
  funext j
  by_cases hj : j = j₀
  · exact hj ▸ h0
  · have := e (fun l => Pi.single (M := fun _ => Ω) j₀ 1 l + Pi.single (M := fun _ => Ω) j 1 l) (by simp [Ne.symm hj])
    simpa [Pi.single_apply, mul_add, Finset.sum_add_distrib, h0] using this

theorem genPt_ratio (j₀ : J) (B : Matrix J J Ω) (hB : B.det ≠ 0) (i : J) :
    (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) i ≠ 0 ∧ AlgebraicIndependent Ω fun j : {j // j ≠ i} =>
      (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) j.1 / (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) i := by
  set u := (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) with hu
  have hi : u i ≠ 0 := fun h => hB (Matrix.det_eq_zero_of_row_eq_zero i
    (congrFun (eq_zero_of_sum_genPt j₀ (B i) h)))
  refine ⟨hi, ?_⟩
  set r : {j // j ≠ i} → _ := fun j => u j.1 / u i
  have hs : (B⁻¹.map (algebraMap Ω _)).mulVec u = genPt Ω j₀ := by
    rw [hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  set K := IntermediateField.adjoin Ω (Set.range r)
  have h1 : ∀ j, u j / u i ∈ K := fun j => by
    by_cases hj : j = i
    · rw [hj, div_self hi]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨j, hj⟩, rfl⟩
  have h2 : ∀ j, genPt Ω j₀ j / u i ∈ K := fun j => by
    rw [← hs, Matrix.mulVec, dotProduct, Finset.sum_div]
    refine sum_mem fun l _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (K.algebraMap_mem _) (h1 l)
  have h3 : K.toSubfield = ⊤ := eq_top_of_genPt_mem j₀ _ K.algebraMap_mem fun j => by
    have := div_mem (h2 j) (h2 j₀)
    rwa [div_div_div_cancel_right₀ hi, genPt_self, div_one] at this
  have h4 : Algebra.IsAlgebraic K (FractionRing (MvPolynomial {j // j ≠ j₀} Ω)) := ⟨fun x =>
    isAlgebraic_algebraMap (⟨x, (h3 ▸ Subfield.mem_top x : x ∈ K.toSubfield)⟩ : K)⟩
  have h5 := IntermediateField.isAlgebraic_adjoin_iff_top.1 h4
  refine (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω r ?_).1
  have h6 := trdeg_add_eq Ω (MvPolynomial {j // j ≠ j₀} Ω) (A := FractionRing (MvPolynomial {j // j ≠ j₀} Ω))
  rw [← h6, MvPolynomial.trdeg_of_isDomain]
  refine le_trans (le_of_eq ?_) le_self_add
  simp [Cardinal.mk_fintype]

end Generic

theorem exists_projBundle : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] (EE : M.Lat J), IsProjOver M.s → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : J → Ω'), ProjBundle M EE M' φ f s ∧ IsProjOver M'.s := by
  intro F Ω _ _ _ M J _ inst ⟨j₀⟩ EE hM
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  letI : DecidableEq J := fun a b => Classical.propDecidable (a = b)
  let Ω' := FractionRing (MvPolynomial {j // j ≠ j₀} Ω)
  let φ : Ω →ₐ[F] Ω' := IsScalarTower.toAlgHom F Ω Ω'
  obtain ⟨M', f, hf, hp, hc⟩ := RatModel.exists_projBundle_closure F Ω M Ω' φ J EE (genPt Ω j₀) hM
    ⟨j₀, by rw [genPt_self]; exact one_ne_zero⟩
    (eq_top_of_genPt_mem j₀ _ (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      fun j => Subfield.subset_closure (Or.inr ⟨j₀, j, by rw [genPt_self, div_one]⟩))
  refine ⟨Ω', inferInstance, inferInstance, M', φ, f, genPt Ω j₀, ⟨hf, fun B hB i => ?_, hc⟩, hp⟩
  obtain ⟨h1, h2⟩ := genPt_ratio j₀ B hB i
  exact ⟨h1, fun P hP => algebraicIndependent_iff.1 h2 P hP⟩

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedEffectiveCartierDivisorPullback
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

noncomputable section

namespace GlobalTheory.FlagBundle.DivPull

variable {F : Type} [Field F] {B Y : GlobalTheory.ProjVar.Var F} {φ : B.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ B.X}

theorem regAt_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : RegAt (f y) g) :
    RegAt y (φ g) :=
  mem_O_ratOf.1 (h.map_mem_O (z := y) (mem_O_ratOf.2 hg))

theorem unitAt_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : UnitAt (f y) g) :
    UnitAt y (φ g) :=
  (unitAt_iff ((map_ne_zero φ).2 hg.ne_zero)).2
    ⟨regAt_map h hg.regAt, by rw [← map_inv₀]; exact regAt_map h hg.inv.regAt⟩

theorem unitAt_of_map (h : (ratOf B).IsHom (ratOf Y) φ f) {y : Y.X} {g : B.Fn} (hg : RegAt (f y) g)
    (hu : UnitAt y (φ g)) : UnitAt (f y) g := by
  have h0 : g ≠ 0 := (map_ne_zero φ).1 hu.ne_zero
  exact (unitAt_iff h0).2 ⟨hg, mem_O_ratOf.1
    (h.inv_mem_O (z := y) (mem_O_ratOf.2 hg) h0 (mem_O_ratOf.2 hu.inv.regAt))⟩

theorem exists_pullback (h : (ratOf B).IsHom (ratOf Y) φ f) (D : B.Dv) :
    ∃ D' : Y.Dv, ∀ (y : Y.X) (g : B.Fnˣ), D.IsEqn (f y) g →
      D'.IsEqn y (Units.map (φ : B.Fn →* Y.Fn) g) := by
  choose e he using fun y : Y.X => D.exists_isEqn (f y)
  have key : ∀ (y : Y.X) (g : B.Fnˣ), D.IsEqn (f y) g →
      germOf y (Units.map (φ : B.Fn →* Y.Fn) (e y)) = germOf y (Units.map (φ : B.Fn →* Y.Fn) g) := by
    intro y g hg
    rw [germOf_eq_iff]
    have := unitAt_map h ((he y).iff_unitAt.1 hg)
    rw [map_div₀] at this
    exact this
  refine ⟨show cartierGroup Y.X from ⟨fun y => germOf y (Units.map (φ : B.Fn →* Y.Fn) (e y)), fun y => ?_⟩, key⟩
  obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (f y)
  exact ⟨f ⁻¹ᵁ U, hU, Units.map (φ : B.Fn →* Y.Fn) g, fun z hz => key z g (hg _ hz)⟩

theorem exists_reduced_pullback : ∀ (F : Type) [Field F] (B Y : GlobalTheory.ProjVar.Var F) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X) (D : B.Dv), (ratOf B).IsHom (ratOf Y) φ f → KeepsRad (ratOf B) (ratOf Y) φ f → D.Eff → (∀ (y : B.X) (g : B.Fnˣ), D.IsEqn y g → ∀ (a : B.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g)) → ∃ D' : Y.Dv, D'.Eff ∧ (∀ y, y ∈ D'.supp ↔ f y ∈ D.supp) ∧ ∀ (y : Y.X) (g : Y.Fnˣ), D'.IsEqn y g → ∀ (a : Y.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g) := by
  intro F _ B Y φ f D h hk hD hr
  obtain ⟨D', hD'⟩ := exists_pullback h D
  refine ⟨D', CartierDiv.eff_iff.2 fun y g hg => ?_, fun y => ?_, fun y g hg a n ha hn => ?_⟩
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    have h1 := ((hD' y e he).iff_unitAt.1 hg).regAt.mul (regAt_map h (CartierDiv.eff_iff.1 hD _ e he))
    have h0 : φ e ≠ 0 := (map_ne_zero φ).2 e.ne_zero
    have e1 : (g : Y.Fn) / φ e * φ e = g := div_mul_cancel₀ _ h0
    exact e1 ▸ h1
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    change ¬ D'.IsEqn y 1 ↔ ¬ D.IsEqn (f y) 1
    rw [not_iff_not, (hD' y e he).iff_unitAt, he.iff_unitAt, Units.val_one, Units.val_one, one_div, one_div]
    constructor
    · intro hu
      have := hu.inv
      rw [inv_inv] at this
      exact (unitAt_of_map h (CartierDiv.eff_iff.1 hD _ e he) this).inv
    · intro hu
      have := hu.inv
      rw [inv_inv] at this
      exact (unitAt_map h this).inv
  · obtain ⟨e, he⟩ := D.exists_isEqn (f y)
    have hR := hk y e ⟨e.ne_zero, mem_O_ratOf.2 (CartierDiv.eff_iff.1 hD _ e he), fun x m hx hm =>
      mem_O_ratOf.2 (hr _ e he x m (mem_O_ratOf.1 hx) (mem_O_ratOf.1 hm))⟩
    have hu : UnitAt y ((g : Y.Fn) / φ e) := (hD' y e he).iff_unitAt.1 hg
    have h0 : φ e ≠ 0 := (map_ne_zero φ).2 e.ne_zero
    have hg0 : (g : Y.Fn) ≠ 0 := g.ne_zero
    have e1 : a ^ n / g * ((g : Y.Fn) / φ e) = a ^ n / φ e := by field_simp
    have e2 : a / φ e * ((g : Y.Fn) / φ e)⁻¹ = a / g := by field_simp
    have h2 : RegAt y (a / φ e) :=
      mem_O_ratOf.1 (hR.2.2 a n (mem_O_ratOf.2 ha) (mem_O_ratOf.2 (e1 ▸ hn.mul hu.regAt)))
    exact e2 ▸ h2.mul hu.inv.regAt

end GlobalTheory.FlagBundle.DivPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtMCastSuccLast
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.TilX

section Ext

variable {A : Type} [CommRing A] {N n : ℕ} (hN : N = n + 1)

def extM (_hN : N = n + 1) (g : Matrix (Fin n) (Fin n) A) : Matrix (Fin N) (Fin N) A := fun a b =>
  if ha : a.1 < n then (if hb : b.1 < n then g ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0) else if b.1 < n then 0 else 1

theorem extM_castSucc (g : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    extM (rfl : n + 1 = n + 1) g i.castSucc j.castSucc = g i j := by
  simp [extM]

theorem extM_castSucc_last (g : Matrix (Fin n) (Fin n) A) (i : Fin n) :
    extM (rfl : n + 1 = n + 1) g i.castSucc (Fin.last n) = 0 := by
  simp [extM]

theorem extM_last_castSucc (g : Matrix (Fin n) (Fin n) A) (j : Fin n) :
    extM (rfl : n + 1 = n + 1) g (Fin.last n) j.castSucc = 0 := by
  simp [extM]

theorem extM_last_last (g : Matrix (Fin n) (Fin n) A) :
    extM (rfl : n + 1 = n + 1) g (Fin.last n) (Fin.last n) = 1 := by
  simp [extM]

theorem extM_mulVec_iC (g : Matrix (Fin n) (Fin n) A) (x : Fin N → A) (i : Fin n) :
    (extM hN g *ᵥ x) (Br.iC hN i) = (g *ᵥ iniH hN x) i := by
  subst hN
  have e : Br.iC (rfl : n + 1 = n + 1) i = i.castSucc := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, e, extM_castSucc, extM_castSucc_last, zero_mul, add_zero]
  rfl

theorem extM_mulVec_iL (g : Matrix (Fin n) (Fin n) A) (x : Fin N → A) :
    (extM hN g *ᵥ x) (Br.iL hN) = x (Br.iL hN) := by
  subst hN
  have e : Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, e, extM_last_castSucc, extM_last_last, zero_mul,
    Finset.sum_const_zero, zero_add, one_mul]

theorem extM_one : extM hN (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  subst hN
  ext a b
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [extM_last_last]
  · rw [extM_last_castSucc, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
  · rw [extM_castSucc_last, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  · rw [extM_castSucc, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castSucc_inj]

theorem extM_mul (g h : Matrix (Fin n) (Fin n) A) : extM hN (g * h) = extM hN g * extM hN h := by
  subst hN
  ext a b
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [extM_last_last, extM_last_castSucc]
  · simp [extM_last_last, extM_last_castSucc]
  · simp [extM_castSucc_last]
  · simp [extM_castSucc, extM_castSucc_last, Matrix.mul_apply]

def extGL : GL (Fin n) A →* GL (Fin N) A :=
  Units.map { toFun := extM hN, map_one' := extM_one hN, map_mul' := extM_mul hN }

theorem extGL_val (g : GL (Fin n) A) : (extGL hN g : Matrix (Fin N) (Fin N) A) = extM hN g := rfl

theorem extGL_inv_val (g : GL (Fin n) A) :
    ((extGL hN g)⁻¹ : GL (Fin N) A).1 = extM hN ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  rw [← map_inv, extGL_val]

theorem eq_extM {M : Matrix (Fin N) (Fin N) A} {g : Matrix (Fin n) (Fin n) A}
    (h1 : ∀ (a : Fin N) (j : Fin n), M a (Br.iC hN j) = extM hN g a (Br.iC hN j))
    (h2 : ∀ a : Fin N, M a (Br.iL hN) = extM hN g a (Br.iL hN)) : M = extM hN g := by
  subst hN
  ext a b
  refine Fin.lastCases ?_ (fun j => ?_) b
  · exact h2 a
  · exact h1 a j

end Ext

end GlobalTheory.Mem.Col2.TilX

end
end

