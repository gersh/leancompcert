import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk432A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571427717685733, 360571439285628247⟩, ⟨504213876270228828, 504551597797702642⟩, true⟩

def state01 : KState := ⟨⟨360591713199365654, 360591724772851206⟩, ⟨(-372294245045316695), (-371956284030140627)⟩, true⟩

def words00 : List Nat := [360583118716439813, 360583118717028994, 360583118449272940, 360583117911198785, 360583117373043303, 360583116696741964, 360583116547246792, 360583116740716807, 360583116741246554, 360583116865512100]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360623100353860291, 360623111932918098⟩, ⟨(-1728743697993971864), (-1728405496175429260)⟩, true⟩

def words01 : List Nat := [360583117050518449, 360583117235683720, 360583117804666160, 360583118484698845, 360583118670421305, 360583118856181406, 360583119289383872, 360583120134327691, 360583121060115173, 360583121985990091]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597868204641069, 360597879789308134⟩, ⟨(-638294699967033884), (-637956255689076370)⟩, true⟩

def words02 : List Nat := [360583122641701859, 360583122763952356, 360583123421313847, 360583124078817628, 360583124274506512, 360583124275096032, 360583123937354324, 360583123330746607, 360583122724054065, 360583122872843351]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560776861024737, 360560788451248719⟩, ⟨965389233980695531, 965727918512406833⟩, true⟩

def words03 : List Nat := [360583123391583668, 360583123910421815, 360583124159367487, 360583124159957120, 360583123875589438, 360583123453500923, 360583123143368965, 360583123143961410, 360583123100340386, 360583122584424307]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612984187454576, 360612995783242248⟩, ⟨(-1292363375083950266), (-1292024449951010738)⟩, true⟩

def words04 : List Nat := [360583122068400733, 360583121633895433, 360583121701550935, 360583121935989555, 360583121936538722, 360583121729286561, 360583121696171582, 360583121855808047, 360583122384944293, 360583123076253947]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk432A
