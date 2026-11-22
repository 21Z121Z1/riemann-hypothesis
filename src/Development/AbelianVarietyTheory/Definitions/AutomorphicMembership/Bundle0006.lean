import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0241
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ResCharThetaJetPlaceDegOne

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.L2.Host

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def ndLab (N : NData R H what₂) (lab : ∀ k, what₂.FT → N.PlG k → Polynomial (ZMod (H.g k)))
    (h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) : NData R H what₂ :=
  { N with lab := lab, lab_monic := h }

structure CGK {N : NData R H what₂} (A : NAut N) where
  CG : ℕ → Type
  csd : ∀ {a}, CG a → Prop
  ralg : ∀ {a}, CG a → Prop
  locG : ∀ {a}, CG a → ∀ w, A.LP w
  locG_dim : ∀ {a} (π : CG a) w, A.lpDim (locG π w) = a
  locG_unr_ae : ∀ {a} (π : CG a), ∀ᶠ w in Filter.cofinite, A.unr (locG π w)
  tw : ∀ {a}, CG a → CG 1 → CG a
  locG_tw : ∀ {a} (π : CG a) (χ : CG 1) w, locG (tw π χ) w = A.lpChar (locG π w) (locG χ w)
  infG : ∀ {a}, CG a → (H.E →+* ℂ) → Multiset ℂ
  infG_card : ∀ {a} (π : CG a) τ, Multiset.card (infG π τ) = a
  ralg_def : ∀ {a} (π : CG a), ralg π ↔ ∀ τ, (infG π τ).Nodup ∧
    ∀ z ∈ infG π τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  infG_tw : ∀ {a} (π : CG a) (χ : CG 1) τ (s : ℂ), infG χ τ = {s} → infG (tw π χ) τ = (infG π τ).map (· + s)
  csd_tw : ∀ {a} (π : CG a) (χ : CG 1), csd χ → csd π → csd (tw π χ)
  csd_unr : ∀ {a} (π : CG a) w w', csd π → IsConjPl H w w' → A.unr (locG π w) →
    A.unr (locG π w') ∧ A.frobEig (locG π w') = (A.frobEig (locG π w)).map (·⁻¹)
  etaT : CG 1
  etaTinv : CG 1
  etaT_unr : ∀ w, A.unr (locG etaT w)
  etaT_inert : ∀ w, ¬ IsSplitPl H w → A.frobEig (locG etaT w) = {-1}
  etaTinv_def : ∀ w, A.unr (locG etaTinv w) ∧ A.frobEig (locG etaTinv w) = (A.frobEig (locG etaT w)).map (·⁻¹)
  etaT_split : ∀ w w', IsSplitPl H w → IsConjPl H w w' → ∀ a b : ℂ, A.frobEig (locG etaT w) = {a} →
    A.frobEig (locG etaT w') = {b} → a * b = 1

def CGK.naut {N : NData R H what₂} {A : NAut N} (K : CGK A) (hE : IsEmpty N.Loc) : NAut N :=
  { A with
    CG := K.CG
    csd := K.csd
    ralg := K.ralg
    locG := K.locG
    locG_dim := K.locG_dim
    locG_unr_ae := K.locG_unr_ae
    tw := K.tw
    locG_tw := K.locG_tw
    infG := K.infG
    infG_card := K.infG_card
    ralg_def := K.ralg_def
    infG_tw := K.infG_tw
    csd_tw := K.csd_tw
    csd_unr := K.csd_unr
    etaT := K.etaT
    etaTinv := K.etaTinv
    etaT_unr := K.etaT_unr
    etaT_inert := K.etaT_inert
    etaTinv_def := K.etaTinv_def
    etaT_split := K.etaT_split
    muC := fun i => hE.elim i
    muC_csd := fun i => hE.elim i
    jumpsInf := fun i => hE.elim i
    jumpsInf_def := fun i => hE.elim i
    chi_mu := fun i => hE.elim i }

end

structure RowWD (D : D7) where
  par : D.what₂.FT → ∀ w : PlE D.host, GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w)
  sat : D.what₂.FT → PlE D.host → Multiset ℂ
  dim : ∀ σ w, (par σ w).lpDim = D.R.r
  tame : ∀ σ k v, (par σ (D.naut.plGw k v)).tame

set_option maxHeartbeats 2000000 in

def setAut (D : D7) (hE : IsEmpty D.nd.Loc) (lab : ∀ k, D.what₂.FT → D.nd.PlG k → Polynomial (ZMod (D.host.g k)))
    (h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = D.R.r) (A : NAut (ndLab D.nd lab h)) (C : NBC A)
    (tg_mem : ∀ k v, D.ntypes.tg k v ∈ Ine (F := D.host.E) (D.nd.plOm.1 (A.plGw k v)))
    (tg_gen : ∀ k v, TameGenAt (D.nd.plOm.1 (A.plGw k v)) (D.ntypes.tg k v))
    (hl : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod) : D7 :=
  { D with
    nd := ndLab D.nd lab h, ntw := { D.ntw with }, naut := A, nbc := C, nexp := { D.nexp with }, nth := { D.nth with }
    ntypes := { D.ntypes with
      tg_mem := tg_mem, tg_gen := tg_gen, heckeLoc_gamma_places := fun i => hE.elim i, inertiaCharpoly_type := hl, chiT_tg := fun i => hE.elim i
      Par := PEmpty, labPar := fun _ a => a.elim, labPar_monic := fun _ a => a.elim, locPar := fun a => a.elim
      locPar_dim := fun a => a.elim, labPar_def := fun _ a => a.elim, MtPar := fun _ _ a => a.elim
      AmbPar := fun _ a => a.elim }
    nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq, ntwbr := D.ntwbr, ntwbr_ind := D.ntwbr_ind
    nbr := fun i => hE.elim i, nbr_ind := fun i => hE.elim i, self_good := fun i => hE.elim i
    loc_tie := fun i => hE.elim i, bc_tie := fun i => hE.elim i, rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i, Z_tie := fun i => hE.elim i, Zgood_tie := fun i => hE.elim i
    etaJ_tie := D.etaJ_tie }

set_option maxHeartbeats 2000000 in

def setCG (D : D7) (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) : D7 :=
  { D with
    naut := K.naut hE, nbc := { D.nbc with }, ntypes := { D.ntypes with }, nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq
    nbr := fun i => hE.elim i, nbr_ind := fun i => hE.elim i, self_good := fun i => hE.elim i
    loc_tie := fun i => hE.elim i, bc_tie := fun i => hE.elim i, rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i, Z_tie := fun i => hE.elim i, Zgood_tie := fun i => hE.elim i }

def setBC (D : D7) (C : NBC D.naut) : D7 := { D with nbc := C }

def setTy (D : D7) (hE : IsEmpty D.nd.Loc) (X : NTypes D.naut) (h1 : X.IdempotentMatchesAction)
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) = X.e0.coeff g) : D7 :=
  { D with
    ntypes := X, nStage_trivialCharacter_compat := h1, nStage_trivialCharacter_coeff_eq := h0
    bc_tie := fun i => hE.elim i, rbar_tie := fun i => hE.elim i, mtpar_tie := fun i => hE.elim i }

def BlocksUnique (D : D7) : Prop :=
  ∀ Sig Sig' : List (Part D.naut.CG), (∀ p ∈ Sig ++ Sig', 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π ∧ ∀ τ, (D.naut.infG p.π τ).Nodup ∧
      ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2) →
    rankIso D.nd D.naut Sig = D.R.r → rankIso D.nd D.naut Sig' = D.R.r →
    (∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Sig w = isoLoc D.nd D.naut Sig' w) →
    Multiset.ofList (Sig.map fun p => (p.a, p.d)) = Multiset.ofList (Sig'.map fun p => (p.a, p.d))

def IsRepOf (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep ρ ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((ρ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
      galPol D.naut (D.naut.lpTw (D.naut.locG π w) s)

def GalEx (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ ρ, IsRepOf D l ι π ((1 - (a : ℝ)) / 2) ρ

def RowCusp (D : D7) (Rw : RowSide D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∃ π : D.naut.CG D.R.r,
    D.naut.csd π ∧ D.naut.ralg π ∧ (∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w) ∧
    ∀ᶠ w in Filter.cofinite, ∃ p : Polynomial ↥D.LL0, p.map (embLL0 D) =
      galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2))

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EisGEqZeroOfInfinite
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField

namespace GlobalTheory.Mem.Per.Model

theorem eisG_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) (k : ℕ) :
    eisG (Λ.map (AddMonoidHom.mulLeft δ)) k = (δ ^ (2 * k))⁻¹ * eisG Λ k := by
  unfold eisG
  rw [← tsum_mul_left]
  let f : {w : ℂ // w ∈ Λ ∧ w ≠ 0} → {w : ℂ // w ∈ Λ.map (AddMonoidHom.mulLeft δ) ∧ w ≠ 0} :=
    fun w => ⟨δ * w.1, ⟨w.1, w.2.1, rfl⟩, mul_ne_zero hδ w.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (mul_left_cancel₀ hδ (congrArg Subtype.val h))
    · rintro ⟨w, ⟨v, hv, rfl⟩, h0⟩
      refine ⟨⟨v, hv, ?_⟩, rfl⟩
      rintro rfl
      simp at h0
  rw [← (Equiv.ofBijective f hf).tsum_eq]
  refine tsum_congr fun w => ?_
  simp [f, mul_pow, mul_comm]

theorem discr_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    TaylorLogMetric.discr (Λ.map (AddMonoidHom.mulLeft δ)) = (δ ^ 12)⁻¹ * TaylorLogMetric.discr Λ := by
  unfold TaylorLogMetric.discr g2 g3
  rw [eisG_map _ _ hδ, eisG_map _ _ hδ]
  field_simp
  ring

theorem jLat_map (Λ : AddSubgroup ℂ) (δ : ℂ) (hδ : δ ≠ 0) :
    jLat (Λ.map (AddMonoidHom.mulLeft δ)) = jLat Λ := by
  unfold jLat
  rw [discr_map _ _ hδ]
  unfold g2
  rw [eisG_map _ _ hδ]
  by_cases h : TaylorLogMetric.discr Λ = 0
  · simp [h]
  · field_simp
    ring

variable {LL : Type} [Field LL] [NumberField LL]

theorem exists_isConjLat_self (emb : LL →+* ℂ) (Λ : AddSubgroup ℂ) (h : TaylorLogMetric.discr Λ ≠ 0)
    (ha : ∃ a : LL, emb a = jLat Λ) : ∃ Λ', IsConjLat emb emb Λ Λ' := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr Λ) (n := 12) (by norm_num)
  have h0 : δ ≠ 0 := by rintro rfl; apply h; rw [← hδ]; simp
  obtain ⟨a, ha⟩ := ha
  refine ⟨Λ.map (AddMonoidHom.mulLeft δ), ?_, a, ha, ?_⟩
  · rw [discr_map _ _ h0, hδ, inv_mul_cancel₀ h]
  · rw [jLat_map _ _ h0, ha]

theorem eisG_eq_zero_of_infinite (Λ : AddSubgroup ℂ) (h : {w : ℂ | w ∈ Λ ∧ w ≠ 0 ∧ ‖w‖ ≤ 1}.Infinite) (k : ℕ) :
    eisG Λ k = 0 := by
  unfold eisG
  apply tsum_eq_zero_of_not_summable
  intro hs
  have ht := hs.tendsto_cofinite_zero
  have he := (Metric.tendsto_nhds.1 ht) 1 one_pos
  rw [Filter.eventually_cofinite] at he
  apply h
  refine (he.image Subtype.val).subset ?_
  rintro w ⟨h1, h2, h3⟩
  refine ⟨⟨w, h1, h2⟩, ?_, rfl⟩
  simp only [Set.mem_setOf_eq, dist_zero_right, not_lt, norm_div, norm_one, norm_pow]
  have hp : 0 < ‖w‖ ^ (2 * k) := pow_pos (norm_pos_iff.2 h2) _
  rw [le_div_iff₀ hp, one_mul]
  exact pow_le_one₀ (norm_nonneg _) h3

theorem finite_of_isConjLat {emb s : LL →+* ℂ} {Λ Λ' : AddSubgroup ℂ} (h : IsConjLat emb s Λ Λ') :
    {w : ℂ | w ∈ Λ' ∧ w ≠ 0 ∧ ‖w‖ ≤ 1}.Finite := by
  by_contra hi
  have := h.1
  unfold TaylorLogMetric.discr g2 g3 at this
  rw [eisG_eq_zero_of_infinite _ hi, eisG_eq_zero_of_infinite _ hi] at this
  norm_num at this

theorem ne_bot_of_isConjLat {emb s : LL →+* ℂ} {Λ Λ' : AddSubgroup ℂ} (h : IsConjLat emb s Λ Λ') : Λ' ≠ ⊥ := by
  rintro rfl
  have := h.1
  haveI : IsEmpty {w : ℂ // w ∈ (⊥ : AddSubgroup ℂ) ∧ w ≠ 0} := ⟨fun w => w.2.2 (AddSubgroup.mem_bot.1 w.2.1)⟩
  unfold TaylorLogMetric.discr g2 g3 eisG at *
  rw [tsum_empty, tsum_empty] at *
  norm_num at *

variable {R : Ranks} (H : Host R)

theorem ellLat_ne_bot (embE : H.E →+* LL) (g : R.GG) : ellLat H embE g ≠ ⊥ := by
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  have hb : H.𝔟 ≠ ⊥ := by
    intro h0
    apply hd
    have := H.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at this
    exact this
  have hA : H.AA0 ≠ 0 := by
    unfold Host.AA0
    exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb)
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hA |>.imp fun a h => h
  obtain ⟨b, hb1, hb0⟩ := (Submodule.ne_bot_iff _).1 hd
  intro h
  have : embE (H.sigmaOf g ((a : H.E) * (b : H.E))) ∈ ellLat H embE g :=
    Submodule.subset_span ⟨_, ha, b, hb1, rfl⟩
  rw [h, Submodule.mem_bot] at this
  simp [ha0, hb0] at this

theorem ne_zero_of_isGen {embE : H.E →+* LL} {g : R.GG} {x : LL} (h : IsGen H embE g x) : x ≠ 0 := by
  rintro rfl
  apply ellLat_ne_bot H embE g
  rw [← h]; simp

theorem gen_spec {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) (g) :
    IsGen H embE g (gen H embE g) := Classical.epsilon_spec (h.2 g)

theorem prod_norm_eq_of_isGen {embE : H.E →+* LL} {g : R.GG} {x y : LL}
    (hx : IsGen H embE g x) (hy : IsGen H embE g y) :
    ∏ s : LL →+* ℂ, ‖s x‖ = ∏ s : LL →+* ℂ, ‖s y‖ := by
  have h : Submodule.span (𝓞 LL) {x} = Submodule.span (𝓞 LL) {y} := hx.trans hy.symm
  obtain ⟨u, hu⟩ := Submodule.span_singleton_eq_span_singleton.1 h
  have hu1 : ∏ s : LL →+* ℂ, ‖s ((u : 𝓞 LL) : LL)‖ = 1 := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom LL ℂ) (fun f => ‖f ((u : 𝓞 LL) : LL)‖)
      (fun φ => ‖φ ((u : 𝓞 LL) : LL)‖) (fun _ => rfl), ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ]
    have := NumberField.Units.norm LL u
    simp only [eq_ratCast, Complex.norm_ratCast]
    exact_mod_cast this
  rw [← hu]
  simp only [Units.smul_def, Algebra.smul_def, map_mul, norm_mul, Finset.prod_mul_distrib]
  rw [show (∏ s : LL →+* ℂ, ‖s (algebraMap (𝓞 LL) LL u)‖) = 1 from hu1, one_mul]

theorem area_pos_of_isConjLat {emb s : LL →+* ℂ} {Λ Λ' : AddSubgroup ℂ} (h : IsConjLat emb s Λ Λ') :
    (∃ L : PeriodPair, ∀ z, z ∈ Λ' ↔ z ∈ L.lattice) ∧ 0 < area Λ' := by
  obtain ⟨L, hL⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_discr_ne_zero (Λ := Λ') (by rw [h.1]; exact one_ne_zero)
  exact ⟨⟨L, hL⟩, (GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ' hL).1⟩

theorem exists_isConjLat (emb s : LL →+* ℂ) (Λ : AddSubgroup ℂ) (ha : ∃ a : LL, emb a = jLat Λ) :
    ∃ Λ', IsConjLat emb s Λ Λ' := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (s a / 1728) (n := 3) (by norm_num)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((s a / 1728 - 1) / 27) (n := 2) (by norm_num)
  have h1 : x ^ 3 - 27 * y ^ 2 = 1 := by rw [hx, hy]; ring
  obtain ⟨L, h2, h3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants (a := x) (b := y)
    (by rw [h1]; exact one_ne_zero)
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hD : TaylorLogMetric.discr L.lattice.toAddSubgroup = 1 := by
    unfold TaylorLogMetric.discr; rw [hd.1, hd.2.1, h2, h3, h1]
  refine ⟨L.lattice.toAddSubgroup, hD, a, ha, ?_⟩
  unfold jLat
  rw [hD, hd.1, h2, hx]; ring

theorem conjLat_spec {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) (s : LL →+* ℂ) :
    IsConjLat emb s (baseLat H) (conjLat H emb s) :=
  Classical.epsilon_spec (exists_isConjLat emb s _ h.1)

theorem om_eq {emb : LL →+* ℂ} {embE : H.E →+* LL} (h : FieldOK H emb embE) {I : Type}
    (e : I ≃ R.Psi) (τ : I) (s : LL →+* ℂ) :
    (trueGx H emb embE e).Om τ s = area (conjLat H emb s) / (Real.pi * ‖s (gen H embE (e τ).1)‖ ^ 2) := by
  have h1 := (area_pos_of_isConjLat (conjLat_spec H h s)).2
  have h2 : s (gen H embE (e τ).1) ≠ 0 := (map_ne_zero s).2 (ne_zero_of_isGen H (gen_spec H h _))
  have h3 : 0 < omAt H emb s (gen H embE (e τ).1) := by
    unfold omAt
    have := norm_pos_iff.2 h2
    have := Real.pi_pos
    positivity
  show posOr1 _ = _
  unfold posOr1
  rw [if_pos h3]; rfl

end GlobalTheory.Mem.Per.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

def LabConj (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) : Prop :=
  ∀ k v (w : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w → ∃ (c : D.nd.Om ≃+* D.nd.Om) (γ : G D.host.E D.nd.Om),
    (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
    (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ (∀ x, γ (c x) = c (D.ntypes.tg k v x)) ∧
    ∀ a : D.naut.LP w, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      D.naut.items₂ k w a = GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ (T.e w a)

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
section
noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.Mem

def retie (D : D7) : D7 :=
  letI := D.host.cmStar
  { D with
    vol := fun W => Vol.trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W
    vol_pos := fun W => Vol.trueVol_pos D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W
    dsig := fun τ => Per.posOr1 (Vol.trueDsig D.R (D.hc τ))
    dsig_pos := fun _ => Per.posOr1_pos _
    s := { D.s with cdScale := Vol.trueScale D.cd, cdScale_pos := Vol.trueScale_pos D.cd }
    gx := Per.trueGx D.host D.what₂.embLL D.embE D.eTau }

end GlobalTheory.Mem
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WithTrue
section
noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.Mem

def GJStage.withTrue {B : Base} {C : Cols B} (G : GJStage B C) : GJStage B C :=
  letI := B.host.cmStar
  { G with
    vol := fun W => Vol.trueVol B.sp.cm (fun g : Tau B.R => B.host.emb g.1) G.cd W
    vol_pos := fun W => Vol.trueVol_pos B.sp.cm (fun g : Tau B.R => B.host.emb g.1) G.cd W
    gx := Per.trueGx B.host B.embLL B.embE (Equiv.refl _) }

def Base.dsigTrue (B : Base) (τ : Tau B.R) : ℝ := Vol.trueDsig B.R (B.hc τ)

end GlobalTheory.Mem
end
end

