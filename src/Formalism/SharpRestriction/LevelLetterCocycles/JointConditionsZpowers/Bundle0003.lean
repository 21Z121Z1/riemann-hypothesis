import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfJointCond
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem rootsBar_mul (a b : (ZMod g)[X]) (ha : a ≠ 0) (hb : b ≠ 0) :
    Formalism.CyclotomicNorms.rootsBar (a * b) = Formalism.CyclotomicNorms.rootsBar a + Formalism.CyclotomicNorms.rootsBar b := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_mul, Polynomial.roots_mul]
  have hi : Function.Injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) := (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
  exact mul_ne_zero ((Polynomial.map_ne_zero_iff hi).2 ha) ((Polynomial.map_ne_zero_iff hi).2 hb)

theorem rootsBar_pow (a : (ZMod g)[X]) (d : ℕ) : Formalism.CyclotomicNorms.rootsBar (a ^ d) = d • Formalism.CyclotomicNorms.rootsBar a := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, Polynomial.roots_pow]

theorem rootsBar_one : Formalism.CyclotomicNorms.rootsBar (1 : (ZMod g)[X]) = 0 := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_one, Polynomial.roots_one]
  rfl

theorem card_rootsBar (a : (ZMod g)[X]) : Multiset.card (Formalism.CyclotomicNorms.rootsBar a) = a.natDegree := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits (a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)))),
    Polynomial.natDegree_map]

theorem rootsBar_frob (a : (ZMod g)[X]) :
    (Formalism.CyclotomicNorms.rootsBar a).map (fun x => x ^ g) = Formalism.CyclotomicNorms.rootsBar a := by
  unfold Formalism.CyclotomicNorms.rootsBar
  have hbij : Function.Bijective (frobenius (Formalism.CyclotomicNorms.Fbar g) g) := PerfectRing.bijective_frobenius
  let F : Formalism.CyclotomicNorms.Fbar g ≃+* Formalism.CyclotomicNorms.Fbar g := RingEquiv.ofBijective (frobenius (Formalism.CyclotomicNorms.Fbar g) g) hbij
  have h1 : ((a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))).map (F : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g)) =
      a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) := by
    rw [Polynomial.map_map]
    congr 1
    ext c
    show (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c) ^ g = _
    rw [← map_pow, ZMod.pow_card]
  have h2 := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := a.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))) (f := (F : Formalism.CyclotomicNorms.Fbar g →+* Formalism.CyclotomicNorms.Fbar g)) F.injective
    (Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _))
  rw [h1] at h2
  exact h2

end Roots

theorem rootsBar_list_prod {g : ℕ} [Fact g.Prime] (l : List (ZMod g)[X]) (h : ∀ a ∈ l, a ≠ 0) :
    Formalism.CyclotomicNorms.rootsBar l.prod = (l.map Formalism.CyclotomicNorms.rootsBar).sum := by
  induction l with
  | nil => exact rootsBar_one
  | cons a l ih =>
    have hl : ∀ b ∈ l, b ≠ 0 := fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [List.prod_cons, List.map_cons, List.sum_cons,
      rootsBar_mul a l.prod (h a List.mem_cons_self) (List.prod_ne_zero (fun h0 => hl 0 h0 rfl)), ih hl]

section Lab

variable (D : D7)
  (hTw : ∀ (k : Fin 2) (w : PlE D.host) (a : D.naut.LP w) (s : ℝ),
    D.naut.items₂ k w (D.naut.lpTw a s) = D.naut.items₂ k w a)

include hTw

theorem inertiaCharpoly_speh_eq_pow (k : Fin 2) (w : PlE D.host) (p : BasicNotions.Part D.naut.CG) :
    D.naut.items₂ k w (spehLoc D.nd D.naut p w) = (D.naut.items₂ k w (D.naut.locG p.π w)) ^ p.d := by
  have key : ∀ l : List ℝ, D.naut.items₂ k w (l.foldr (fun (j : ℝ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - j)) acc) (D.naut.lpZero w)) =
      (D.naut.items₂ k w (D.naut.locG p.π w)) ^ l.length := by
    intro l
    induction l with
    | nil => simp [D.naut.inertiaCharpoly_zero]
    | cons j l ih => rw [List.foldr_cons, D.naut.inertiaCharpoly_add, hTw, ih, List.length_cons, pow_succ, mul_comm]
  unfold spehLoc
  rw [key]
  simp

theorem inertiaCharpoly_eq_of_iso (k : Fin 2) (w : PlE D.host) (Sig : List (BasicNotions.Part D.naut.CG)) :
    D.naut.items₂ k w (isoLoc D.nd D.naut Sig w) =
      (Sig.map fun p => (D.naut.items₂ k w (D.naut.locG p.π w)) ^ p.d).prod := by
  induction Sig with
  | nil => simp [isoLoc, D.naut.inertiaCharpoly_zero]
  | cons p Sig ih =>
    rw [List.map_cons, List.prod_cons, ← ih, ← inertiaCharpoly_speh_eq_pow D hTw]
    exact D.naut.inertiaCharpoly_add _ _ _ _

end Lab

def IsBcSig (D : D7) (i : D.nd.Loc) (σ : D.what₂.FT) (Sig : List (Part D.naut.CG)) : Prop :=
  D.what₂.isot (D.nd.j i) σ ≠ ⊥ ∧ HasParamW D.nd D.naut i σ Sig ∧ (∃ P, thetaOf D.nd D.naut i σ P) ∧
    ∀ P, thetaOf D.nd D.naut i σ P →
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv)

def GlobalDatumTwistCondition (D : D7) : Prop :=
  (∀ σ : D.what₂.FT, ∃ i : D.nd.Loc, D.what₂.isot (D.nd.j i) σ ≠ ⊥) ∧
  (∀ i σ Sig, IsBcSig D i σ Sig → ∀ p ∈ Sig, D.naut.csd p.π) ∧
  (∀ (k : Fin 2) (w : PlE D.host) (a : D.naut.LP w) (s : ℝ),
    D.naut.items₂ k w (D.naut.lpTw a s) = D.naut.items₂ k w a) ∧
  (∀ i σ Sig, IsBcSig D i σ Sig → ∀ p ∈ Sig, ∀ (k : Fin 2) (v : D.nd.PlG k),
    (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v))).natDegree = p.a) ∧
  (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) ∧
  (∀ i σ Sig, IsBcSig D i σ Sig → ∀ p ∈ Sig, ∀ τ, (D.naut.infG p.π τ).Nodup ∧
    ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2)

def GlobalDatumTwistDualCondition (D : D7) : Prop :=
  ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k),
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (D.ntypes.cuspidal σ →
      Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ D.host.g k →
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      Matrix.charpoly ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v w (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar w) x))).prod ∧
      ∃ φ : G D.host.E D.nd.Om,
        D.ntypes.rbar σ w (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ w (D.ntypes.tg k v) ^ D.host.g k)

theorem archimedeanSignatureMatching_of_jointCond (D : D7) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D) (ha : GlobalDatumTwistCondition D) (hb : GlobalDatumTwistDualCondition D) :
    Formalism.MainNotions.ArithmeticCylinders.ArchimedeanSignatureMatching D := by
  intro σ k v
  refine ⟨?_, hb σ k v⟩
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨hocc, hcsd, hTw, hdz, hsp, hreg⟩ := ha
  obtain ⟨i, hi⟩ := hocc σ
  obtain ⟨Sig, hSig, hBCV⟩ := (h42 i σ hi).2.1
  have hBc : IsBcSig D i σ Sig := ⟨hi, hSig, (h42 i σ hi).1.2, hBCV⟩
  have hlab : D.nd.lab k σ v = (Sig.map fun p =>
      (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v))) ^ p.d).prod := by
    rw [D.naut.lab_loc i k σ v, ← hSig.2.2 _ (hsp k v), inertiaCharpoly_eq_of_iso D hTw]
  have hne : ∀ p ∈ Sig, D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)) ≠ 0 := by
    intro p hp h0
    have h1 := hdz i σ Sig hBc p hp k v
    rw [h0, Polynomial.natDegree_zero] at h1
    have := (hSig.1 p hp).1
    omega
  refine ⟨Sig.map fun p => (p.a, p.d,
    Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)))), ?_, ?_, ?_⟩
  · rw [D.bc_tie i σ Sig hSig (hcsd i σ Sig hBc) (hreg i σ Sig hBc), List.map_map]
    rfl
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact ⟨by rw [card_rootsBar]; exact hdz i σ Sig hBc p hp k v, rootsBar_frob _⟩
  · rw [hlab, rootsBar_list_prod, List.map_map, List.map_map]
    · congr 1
      refine List.map_congr_left fun p _ => ?_
      exact rootsBar_pow _ _
    · intro a ha'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha'
      exact pow_ne_zero _ (hne p hp)

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.DimensionInputTwoOfBlochKato
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem dimension_input_one_of_bloch_kato (D : D7) (h : Formalism.MainNotions.LocalSituation.Conclusion5 D) : Formalism.MainNotions.BlochKatoDuality.adm1 D := by
  intro l _ K
  exact (h l K).1

theorem dimension_input_two_of_bloch_kato (D : D7) (h : Formalism.MainNotions.LocalSituation.Conclusion5 D) : Formalism.MainNotions.BlochKatoDuality.adm2 D := by
  intro l _ K
  exact (h l K).2.2.2.1

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IrreducibilityOfTheoremThree
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

def GlobalDatumCompatibility (D : D7) : Prop :=
  Formalism.MainNotions.SphericalInertData.HypEFK D ∧
    (2 ≤ Module.finrank ℚ D.host.F ∧
      ∀ w : PlE D.host, ¬ IsSplitPl D.host w → ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) ∧
    ∀ j, 1 ≤ j → j ≤ D.R.m → (letI := D.host.cmStar; (D.sp.V j).IsDefinite)

theorem nV_pos (D : D7) : 1 ≤ D.R.nV := by
  have := D.R.t_odd.pos
  show 1 ≤ D.R.r + D.R.t
  omega

theorem hypCM_of (D : D7) (hc : GlobalDatumCompatibility D) : Formalism.MainNotions.SphericalInertData.HypCM D := by
  refine ⟨?_, hc.2.1⟩
  letI := D.host.cmStar
  exact D.sp.cm.cmUnram

theorem base_change_automorphic_of (D : D7) (h45 : Formalism.MainNotions.SphericalInertData.Conclusion1 D) (hc : GlobalDatumCompatibility D) :
    Formalism.MainNotions.SumRepresentations.adm1 D := by
  intro i P
  obtain ⟨Pa, h1, h2, h3, h4, h5, h6⟩ :=
    h45 hc.1 (hypCM_of D hc) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (nV_pos D)
      (hc.2.2 _ (D.nd.j_range i).1 (D.nd.j_range i).2) (D.nbc.embAV i P)
      (fun w hw => D.nbc.embAV_sph i P w hw)
  refine ⟨Pa, h1, h2, h3, fun w hw => (h4 w hw).trans (D.nbc.embAV_loc i P w).symm,
    fun w hw => ⟨(h5 w hw).1, (h5 w hw).2.trans (congrArg _ (D.nbc.embAV_sat i P w).symm)⟩,
    fun τ => (h6 τ).trans (congrFun (D.nbc.embAV_inf i P) τ).symm⟩

def LitBNIrr (Γ : Type) [Group Γ] : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)),
    (∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar ℓ)).charpoly) →
    Formalism.CyclotomicNorms.IrredOn ρ' ⊤ → Formalism.CyclotomicNorms.IrredOn ρ ⊤

theorem charpoly_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ}
    (f : A →+* B) (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL _ _) : Matrix (Fin a) (Fin a) B).charpoly =
      (((ρ g : GL _ _) : Matrix (Fin a) (Fin a) A).charpoly).map f :=
  Matrix.charpoly_map _ f

theorem irredOn_fbCast {Γ : Type} [Group Γ] {p q : ℕ} (h : p = q) (hp : p.Prime) (hq : q.Prime) {a : ℕ}
    (ρ : Γ →* GL (Fin a) (Fb p hp))
    (hρ : @Formalism.CyclotomicNorms.IrredOn a p ⟨hp⟩ Γ _ ρ ⊤) :
    @Formalism.CyclotomicNorms.IrredOn a q ⟨hq⟩ Γ _ (mapRep (fbCast h hp hq).toRingHom ρ) ⊤ := by
  subst h
  have e : mapRep (fbCast rfl hp hq).toRingHom ρ = ρ := by
    ext g i j
    rfl
  rw [e]
  exact hρ

def GlobalDatumRegularity (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (u : (ZMod (D.host.g k))ˣ) (y : D.nd.O i),
    D.nd.l i ≠ D.host.g k →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    D.naut.iotaQC i (D.naut.iotaQ i (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) y)) =
      D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k))) →
    D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y) =
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i))
          (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))))

theorem irreducibility_of_theorem_three (D : D7) (h33 : Formalism.MainNotions.ArithmeticCylinders.PointsLemma D) (hBN : LitBNIrr (G D.host.E D.nd.Om))
    (hc : GlobalDatumRegularity D) : Formalism.MainNotions.SumRepresentations.At.IrreducibilityParameter D.nd D.naut := by
  intro i σ _ hgood Sig hSig ρ hρ
  obtain ⟨-, hw⟩ := h33 D.ntypes.BB_disj σ hgood (fun k v => (D.ntypes.tg_gen k v).2)
  obtain ⟨hirr, -, hroot⟩ := hw (D.nd.w i)
  obtain ⟨-, hcp⟩ := D.rbar_tie i σ Sig ρ hSig hρ
  refine ⟨?_, ?_⟩
  · refine hBN (D.nd.l i) D.R.r _ _ (fun g => ?_)
      (irredOn_fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out _ hirr)
    rw [charpoly_mapRep, charpoly_mapRep]
    exact (hcp g).symm
  · intro k hk v _ hr
    rw [D.ntypes.heckeLoc_gamma_places i k v] at hr
    have hk' : D.what₂.places.resChar (D.nd.w i) ≠ D.host.g k := by rw [D.nd.w_l i]; exact hk
    rw [charpoly_mapRep, ← hcp] at hr
    have hχ : chi1 D.nd i (D.ntypes.tg k v) =
        ((D.nd.chi i 1 (D.ntypes.tg k v) : (D.nd.O i)ˣ) : D.nd.O i) := rfl
    rcases D.ntypes.chiT_tg i k v hk with h | h
    · rw [hχ, hc i k v _ _ hk h] at hr
      exact hroot k hk' v _ _ (Or.inl rfl) (hr.of_map (RingEquiv.injective _))
    · rw [hχ, hc i k v _ _ hk h] at hr
      exact hroot k hk' v _ _ (Or.inr rfl) (hr.of_map (RingEquiv.injective _))

end Formalism.MainNotions.N
end
end

