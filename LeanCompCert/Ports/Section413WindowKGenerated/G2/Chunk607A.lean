import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk607A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557343194408632, 360557366673241580⟩, ⟨1516783510006314261, 1517746298531193761⟩, true⟩

def state01 : KState := ⟨⟨360587134382842059, 360587157869695308⟩, ⟨(-291632393563027706), (-290669118165902656)⟩, true⟩

def words00 : List Nat := [360582370319643506, 360582370106376754, 360582370293062255, 360582370522601313, 360582370523394074, 360582370523558806, 360582370324053537, 360582370215923650, 360582370107552555, 360582370119235492]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360596639402867617, 360596662897823669⟩, ⟨(-868795402292929438), (-867831634934919228)⟩, true⟩

def words01 : List Nat := [360582370120006209, 360582369975966811, 360582369900856497, 360582370108664757, 360582370246916556, 360582370385302979, 360582370386060639, 360582370344239090, 360582370544492251, 360582370780847089]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594507234469263, 360594530737424710⟩, ⟨(-739365023153898139), (-738400770032652231)⟩, true⟩

def words02 : List Nat := [360582371175004804, 360582371381505309, 360582371414239015, 360582371447057608, 360582371447782273, 360582371293841138, 360582371574946706, 360582371856206034, 360582371988478800, 360582372189565583]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608743257997904, 360608766768988195⟩, ⟨(-1604023826497869089), (-1603059085379684593)⟩, true⟩

def words03 : List Nat := [360582372431516297, 360582372673729059, 360582373186744986, 360582373429698704, 360582373443172348, 360582373456716153, 360582373741156932, 360582374184630024, 360582374619846786, 360582375055230113]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360601657596680997, 360601681115778456⟩, ⟨(-1173731386635616500), (-1172766153049099868)⟩, true⟩

def words04 : List Nat := [360582375298286096, 360582375519355615, 360582375726537464, 360582375933959648, 360582376071919328, 360582376216772707, 360582376225302181, 360582376233924416, 360582376322154518, 360582376640904807]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk607A
