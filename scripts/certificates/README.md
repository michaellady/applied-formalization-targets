# Certificate generators (untrusted)

These Python scripts generated the data files `Applied/Statistics/NormalTableData.lean` and
`Applied/Statistics/DobribanCertificate.lean` used in the refutation of `BHTwoSidedGaussian`.
They are not part of the trusted base: Lean's kernel re-checks every table entry and every
certificate bin (`tab_ok`, `chunk*_ok`). They are kept only so the data can be regenerated.

Order: `tabgen.py` (writes `table.pkl`) → `tab2lean.py`; `certgen.py` (writes `cert_*.pkl`) →
`cert2lean.py`.
