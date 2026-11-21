"""Stage DN: the constant of the second term of Lemma CM-1 (paper H v1.1/v1.2, sec. 8):  x E1 <= (1 + b/2) E0 ln(2 B0/E0) + (sqrt2/e) b E0',  E0' <= Qbar^2 = 1/16,
so the term is at most C_CM b with C_CM := sqrt(2)/(16 e) = 0.03251625593893...   Up to stage DM the lab codes used 0.0325 (rounded DOWN by 0.05 %: found in DM).
  C_CM      float (double precision value; for the numerical codes)
  C_CM_DEC  decimal string rounded UP (for the decimal point computations): 0.03251625594
  c_cm_iv() an interval enclosing sqrt(2)/(16 e) (dl_interval, outward rounding), for the interval proofs
The environment variable CM_C0325=1 restores 0.0325 everywhere (to reproduce the records up to stage DM).  Python 3.11 grammar."""
import os, math
OLD = os.environ.get('CM_C0325', '0') != '0'
C_CM = 0.0325 if OLD else math.sqrt(2.0) / (16.0 * math.e)
C_CM_DEC = '0.0325' if OLD else '0.03251625594'


def c_cm_iv():
    import dl_interval as V
    from decimal import Decimal as Dc
    if OLD: return V.Iv(Dc('0.0325'))
    return V.sqrt(V.Iv(2)) / (16 * V.exp(V.Iv(1)))
