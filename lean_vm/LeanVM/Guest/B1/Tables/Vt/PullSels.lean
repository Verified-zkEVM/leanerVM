/-
  LeanVM.Guest.B1.Tables.Vt.PullSels

  The pull side's table block selectors are the push side's, copied.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Base

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vtPullSels0 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1952), σ (.n 1954), σ (.n 1956), σ (.n 1958), σ (.n 1960)] =
      [σ (.n 952), σ (.n 957), σ (.n 962), σ (.n 967), σ (.n 972)] := by
  have a1978 := h.atomAt 1978 (.copy (.n 1952) (.n 952)) (by decide +kernel)
  have a1980 := h.atomAt 1980 (.copy (.n 1954) (.n 957)) (by decide +kernel)
  have a1982 := h.atomAt 1982 (.copy (.n 1956) (.n 962)) (by decide +kernel)
  have a1984 := h.atomAt 1984 (.copy (.n 1958) (.n 967)) (by decide +kernel)
  have a1986 := h.atomAt 1986 (.copy (.n 1960) (.n 972)) (by decide +kernel)
  simp only [Atom.Holds] at a1978 a1980 a1982 a1984 a1986
  rw [a1978, a1980, a1982, a1984, a1986]

theorem vtPullSels1 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1962), σ (.n 1964), σ (.n 1966), σ (.n 1968), σ (.n 1970)] =
      [σ (.n 981), σ (.n 990), σ (.n 999), σ (.n 1008), σ (.n 1017)] := by
  have a1988 := h.atomAt 1988 (.copy (.n 1962) (.n 981)) (by decide +kernel)
  have a1990 := h.atomAt 1990 (.copy (.n 1964) (.n 990)) (by decide +kernel)
  have a1992 := h.atomAt 1992 (.copy (.n 1966) (.n 999)) (by decide +kernel)
  have a1994 := h.atomAt 1994 (.copy (.n 1968) (.n 1008)) (by decide +kernel)
  have a1996 := h.atomAt 1996 (.copy (.n 1970) (.n 1017)) (by decide +kernel)
  simp only [Atom.Holds] at a1988 a1990 a1992 a1994 a1996
  rw [a1988, a1990, a1992, a1994, a1996]

theorem vtPullSels2 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1972), σ (.n 1974), σ (.n 1976)] =
      [σ (.n 1026), σ (.n 1035), σ (.n 1044)] := by
  have a1998 := h.atomAt 1998 (.copy (.n 1972) (.n 1026)) (by decide +kernel)
  have a2000 := h.atomAt 2000 (.copy (.n 1974) (.n 1035)) (by decide +kernel)
  have a2002 := h.atomAt 2002 (.copy (.n 1976) (.n 1044)) (by decide +kernel)
  simp only [Atom.Holds] at a1998 a2000 a2002
  rw [a1998, a2000, a2002]

theorem vtPullSels3 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1978), σ (.n 1980), σ (.n 1982), σ (.n 1984), σ (.n 1986)] =
      [σ (.n 1053), σ (.n 1062), σ (.n 1071), σ (.n 1080), σ (.n 1089)] := by
  have a2004 := h.atomAt 2004 (.copy (.n 1978) (.n 1053)) (by decide +kernel)
  have a2006 := h.atomAt 2006 (.copy (.n 1980) (.n 1062)) (by decide +kernel)
  have a2008 := h.atomAt 2008 (.copy (.n 1982) (.n 1071)) (by decide +kernel)
  have a2010 := h.atomAt 2010 (.copy (.n 1984) (.n 1080)) (by decide +kernel)
  have a2012 := h.atomAt 2012 (.copy (.n 1986) (.n 1089)) (by decide +kernel)
  simp only [Atom.Holds] at a2004 a2006 a2008 a2010 a2012
  rw [a2004, a2006, a2008, a2010, a2012]

theorem vtPullSels4 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1988), σ (.n 1990), σ (.n 1992), σ (.n 1994), σ (.n 1996)] =
      [σ (.n 1098), σ (.n 1107), σ (.n 1116), σ (.n 1125), σ (.n 1134)] := by
  have a2014 := h.atomAt 2014 (.copy (.n 1988) (.n 1098)) (by decide +kernel)
  have a2016 := h.atomAt 2016 (.copy (.n 1990) (.n 1107)) (by decide +kernel)
  have a2018 := h.atomAt 2018 (.copy (.n 1992) (.n 1116)) (by decide +kernel)
  have a2020 := h.atomAt 2020 (.copy (.n 1994) (.n 1125)) (by decide +kernel)
  have a2022 := h.atomAt 2022 (.copy (.n 1996) (.n 1134)) (by decide +kernel)
  simp only [Atom.Holds] at a2014 a2016 a2018 a2020 a2022
  rw [a2014, a2016, a2018, a2020, a2022]

theorem vtPullSels5 {rd : Reader} {σ : Val} (h : VtH rd σ) :
    [σ (.n 1998), σ (.n 2000), σ (.n 2002), σ (.n 2004), σ (.n 2006), σ (.n 2008), σ (.n 2010), σ (.n 2012), σ (.n 2014), σ (.n 2016), σ (.n 2018), σ (.n 2020), σ (.n 2022), σ (.n 2024), σ (.n 2026), σ (.n 2028), σ (.n 2030), σ (.n 2032), σ (.n 2034), σ (.n 2036), σ (.n 2038), σ (.n 2040), σ (.n 2042), σ (.n 2044), σ (.n 2046), σ (.n 2048), σ (.n 2050), σ (.n 2052)] =
      [σ (.n 1143), σ (.n 1152), σ (.n 1161), σ (.n 1170), σ (.n 1179), σ (.n 1188), σ (.n 1197), σ (.n 1206), σ (.n 1215), σ (.n 1224), σ (.n 1233), σ (.n 1242), σ (.n 1251), σ (.n 1260), σ (.n 1269), σ (.n 1278), σ (.n 1287), σ (.n 1296), σ (.n 1305), σ (.n 1314), σ (.n 1323), σ (.n 1332), σ (.n 1341), σ (.n 1350), σ (.n 1359), σ (.n 1368), σ (.n 1377), σ (.n 1386)] := by
  have a2024 := h.atomAt 2024 (.copy (.n 1998) (.n 1143)) (by decide +kernel)
  have a2026 := h.atomAt 2026 (.copy (.n 2000) (.n 1152)) (by decide +kernel)
  have a2028 := h.atomAt 2028 (.copy (.n 2002) (.n 1161)) (by decide +kernel)
  have a2030 := h.atomAt 2030 (.copy (.n 2004) (.n 1170)) (by decide +kernel)
  have a2032 := h.atomAt 2032 (.copy (.n 2006) (.n 1179)) (by decide +kernel)
  have a2034 := h.atomAt 2034 (.copy (.n 2008) (.n 1188)) (by decide +kernel)
  have a2036 := h.atomAt 2036 (.copy (.n 2010) (.n 1197)) (by decide +kernel)
  have a2038 := h.atomAt 2038 (.copy (.n 2012) (.n 1206)) (by decide +kernel)
  have a2040 := h.atomAt 2040 (.copy (.n 2014) (.n 1215)) (by decide +kernel)
  have a2042 := h.atomAt 2042 (.copy (.n 2016) (.n 1224)) (by decide +kernel)
  have a2044 := h.atomAt 2044 (.copy (.n 2018) (.n 1233)) (by decide +kernel)
  have a2046 := h.atomAt 2046 (.copy (.n 2020) (.n 1242)) (by decide +kernel)
  have a2048 := h.atomAt 2048 (.copy (.n 2022) (.n 1251)) (by decide +kernel)
  have a2050 := h.atomAt 2050 (.copy (.n 2024) (.n 1260)) (by decide +kernel)
  have a2052 := h.atomAt 2052 (.copy (.n 2026) (.n 1269)) (by decide +kernel)
  have a2054 := h.atomAt 2054 (.copy (.n 2028) (.n 1278)) (by decide +kernel)
  have a2056 := h.atomAt 2056 (.copy (.n 2030) (.n 1287)) (by decide +kernel)
  have a2058 := h.atomAt 2058 (.copy (.n 2032) (.n 1296)) (by decide +kernel)
  have a2060 := h.atomAt 2060 (.copy (.n 2034) (.n 1305)) (by decide +kernel)
  have a2062 := h.atomAt 2062 (.copy (.n 2036) (.n 1314)) (by decide +kernel)
  have a2064 := h.atomAt 2064 (.copy (.n 2038) (.n 1323)) (by decide +kernel)
  have a2066 := h.atomAt 2066 (.copy (.n 2040) (.n 1332)) (by decide +kernel)
  have a2068 := h.atomAt 2068 (.copy (.n 2042) (.n 1341)) (by decide +kernel)
  have a2070 := h.atomAt 2070 (.copy (.n 2044) (.n 1350)) (by decide +kernel)
  have a2072 := h.atomAt 2072 (.copy (.n 2046) (.n 1359)) (by decide +kernel)
  have a2074 := h.atomAt 2074 (.copy (.n 2048) (.n 1368)) (by decide +kernel)
  have a2076 := h.atomAt 2076 (.copy (.n 2050) (.n 1377)) (by decide +kernel)
  have a2078 := h.atomAt 2078 (.copy (.n 2052) (.n 1386)) (by decide +kernel)
  simp only [Atom.Holds] at a2024 a2026 a2028 a2030 a2032 a2034 a2036 a2038 a2040 a2042 a2044 a2046 a2048 a2050 a2052 a2054 a2056 a2058 a2060 a2062 a2064 a2066 a2068 a2070 a2072 a2074 a2076 a2078
  rw [a2024, a2026, a2028, a2030, a2032, a2034, a2036, a2038, a2040, a2042, a2044, a2046, a2048, a2050, a2052, a2054, a2056, a2058, a2060, a2062, a2064, a2066, a2068, a2070, a2072, a2074, a2076, a2078]

end
end LeanVM.Guest.B1.Tables
