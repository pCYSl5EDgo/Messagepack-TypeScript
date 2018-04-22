//original license
/*
LZ4 Library
Copyright (c) 2011-2016, Yann Collet
All rights reserved.

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice, this
  list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright notice, this
  list of conditions and the following disclaimer in the documentation and/or
  other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

const MEMORY_USAGE = 12;
const NOTCOMPRESSIBLE_DETECTIONLEVEL = 6;
const MINMATCH = 4;
const SKIPSTRENGTH = NOTCOMPRESSIBLE_DETECTIONLEVEL > 2 ? NOTCOMPRESSIBLE_DETECTIONLEVEL : 2;
const COPYLENGTH = 8;
const LASTLITERALS = 5;
const MFLIMIT = COPYLENGTH + MINMATCH;
const MINLENGTH = MFLIMIT + 1;
const MAXD_LOG = 16;
const MAXD = 1 << MAXD_LOG;
const MAXD_MASK = MAXD - 1;
const MAX_DISTANCE = (1 << MAXD_LOG) - 1;
const ML_BITS = 4;
const ML_MASK = (1 << ML_BITS) - 1;
const RUN_BITS = 8 - ML_BITS;
const RUN_MASK = (1 << RUN_BITS) - 1;
const STEPSIZE_64 = 8;
const STEPSIZE_32 = 4;
const LZ4_64KLIMIT = (1 << 16) + (MFLIMIT - 1);
const HASH_LOG = MEMORY_USAGE - 2;
const HASH_TABLESIZE = 1 << HASH_LOG;
const HASH_ADJUST = (MINMATCH * 8) - HASH_LOG;
const HASH64K_LOG = HASH_LOG + 1;
const HASH64K_TABLESIZE = 1 << HASH64K_LOG;
const HASH64K_ADJUST = (MINMATCH * 8) - HASH64K_LOG;
const BLOCK_COPY_LIMIT = 16;
const DECODER_TABLE_32: ReadonlyArray<number> = [0, 3, 2, 3, 0, 0, 0, 0];
const DEBRUIJN_TABLE_32: ReadonlyArray<number> = [
    0, 0, 3, 0, 3, 1, 3, 0, 3, 2, 2, 1, 3, 2, 0, 1,
    3, 3, 1, 2, 2, 2, 2, 0, 3, 1, 2, 0, 1, 0, 1, 1
];

export function getMaximumOutputLength(inputLength: number): number {
    return inputLength + ((inputLength / 255) | 0) + 16;
}

function CheckArguments(input: Uint8Array, inputOffset: number, inputLength: number, output: Uint8Array, outputOffset: number, outputLength: number): void {
    if (inputLength === 0) {
        outputLength = 0;
        return;
    }

    if (inputOffset > input.length) throw ("inputOffset");
    if (inputLength > input.length - inputOffset) throw ("inputLength");

    if (outputOffset > output.length) throw ("outputOffset");
    if (outputLength > output.length - outputOffset) throw ("outputLength");
}

function Poke2(buffer: Uint8Array, offset: number, value: number): void {
    buffer[offset] = value;
    buffer[offset + 1] = value >>> 8;
}

function Peek2(buffer: Uint8Array, offset: number): number {
    return buffer[offset] | (buffer[offset + 1] << 8);
}

function Peek4(buffer: Uint8Array, offset: number): number {
    return buffer[offset++] | (buffer[offset++] << 8) | (buffer[offset++] << 16) | (buffer[offset] << 24);
}

function Xor4(buffer: Uint8Array, offset1: number, offset2: number): number {

    return (buffer[offset1++] | (buffer[offset1++] << 8) | (buffer[offset1++] << 16) | (buffer[offset1] << 24)) ^ ((buffer[offset2++]) | (buffer[offset2++] << 8) | (buffer[offset2++] << 16) | (buffer[offset2] << 24));
}

function Equal2(buffer: Uint8Array, offset1: number, offset2: number): boolean {

    if (buffer[offset1++] !== buffer[offset2++]) return false;
    return buffer[offset1] === buffer[offset2];
}

function Equal4(buffer: Uint8Array, offset1: number, offset2: number): boolean {

    if (buffer[offset1++] !== buffer[offset2++]) return false;
    if (buffer[offset1++] !== buffer[offset2++]) return false;
    if (buffer[offset1++] !== buffer[offset2++]) return false;
    return buffer[offset1] === buffer[offset2];
}

function Copy4(buf: Uint8Array, src: number, dst: number): void {
    buf[dst++] = buf[src++];
    buf[dst++] = buf[src++];
    buf[dst++] = buf[src++];
    buf[dst] = buf[src];
}

function BlockCopy(src: Uint8Array, src_0: number, dst: Uint8Array, dst_0: number, len: number) {
    while (len >= 8) {
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        len -= 8;
    }
    while (len >= 4) {
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        len -= 4;
    }
    while (len-- > 0) {
        dst[dst_0++] = src[src_0++];
    }
}

function WildCopy(src: Uint8Array, src_0: number, dst: Uint8Array, dst_0: number, dst_end: number) {
    let len = dst_end - dst_0;
    while (len >= 8) {
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        len -= 8;
    }
    while (len >= 4) {
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        dst[dst_0++] = src[src_0++];
        len -= 4;
    }
    while (len-- > 0) {
        dst[dst_0++] = src[src_0++];
    }
    return len;
}

function SecureCopy(buffer: Uint8Array, src: number, dst: number, dst_end: number) {
    const diff = dst - src;
    const length = dst_end - dst;
    let len = length;

    if (diff >= BLOCK_COPY_LIMIT) {
        if (diff >= length) {
            buffer.subarray(dst).set(buffer.subarray(src, src + length));
            return length;
        }
        do {
            buffer.subarray(dst).set(buffer.subarray(src, src + diff));
            src += diff;
            dst += diff;
            len -= diff;
        } while (len >= diff);
    }
    while (len >= 4) {
        buffer[dst] = buffer[src];
        buffer[dst + 1] = buffer[src + 1];
        buffer[dst + 2] = buffer[src + 2];
        buffer[dst + 3] = buffer[src + 3];
        dst += 4;
        src += 4;
        len -= 4;
    }
    while (len-- > 0) {
        buffer[dst++] = buffer[src++];
    }
    return length;
}


export function decode(src: Uint8Array, dst: Uint8Array, src_0: number, dst_0: number, dst_len: number): number {
    const dec32table = DECODER_TABLE_32;
    let _i;



    let src_p = src_0;
    let dst_ref;

    let dst_p = dst_0;
    const dst_end = dst_p + dst_len;
    let dst_cpy;

    const dst_LASTLITERALS = dst_end - LASTLITERALS;
    const dst_COPYLENGTH = dst_end - COPYLENGTH;
    const dst_COPYLENGTH_STEPSIZE_4 = dst_end - COPYLENGTH - (STEPSIZE_32 - 4);

    let token;


    while (true) {
        let length;


        token = src[src_p++];
        if ((length = (token >>> ML_BITS)) === RUN_MASK) {
            let len;
            for (; (len = src[src_p++]) === 255; length += 255) {
                /* do nothing */
            }
            length += len;
        }


        dst_cpy = dst_p + length;

        if (dst_cpy > dst_COPYLENGTH) {
            if (dst_cpy !== dst_end) throw "_output_error1";
            BlockCopy(src, src_p, dst, dst_p, length);
            src_p += length;
            break;
        }
        if (dst_p < dst_cpy) {
            _i = WildCopy(src, src_p, dst, dst_p, dst_cpy);
            src_p += _i;
            dst_p += _i;
        }
        src_p -= (dst_p - dst_cpy);
        dst_p = dst_cpy;


        dst_ref = (dst_cpy) - Peek2(src, src_p);
        src_p += 2;
        if (dst_ref < dst_0) throw "_output_error2";


        if ((length = (token & ML_MASK)) === ML_MASK) {
            for (; src[src_p] === 255; length += 255) src_p++;
            length += src[src_p++];
        }


        if ((dst_p - dst_ref) < STEPSIZE_32) {
            const dec64 = 0;
            dst[dst_p + 0] = dst[dst_ref + 0];
            dst[dst_p + 1] = dst[dst_ref + 1];
            dst[dst_p + 2] = dst[dst_ref + 2];
            dst[dst_p + 3] = dst[dst_ref + 3];
            dst_p += 4;
            dst_ref += 4;
            dst_ref -= dec32table[dst_p - dst_ref];
            Copy4(dst, dst_ref, dst_p);
            dst_p += STEPSIZE_32 - 4;
            dst_ref -= dec64;
        }
        else {
            Copy4(dst, dst_ref, dst_p);
            dst_p += 4;
            dst_ref += 4;
        }
        dst_cpy = dst_p + length - (STEPSIZE_32 - 4);

        if (dst_cpy > dst_COPYLENGTH_STEPSIZE_4) {
            if (dst_cpy > dst_LASTLITERALS) throw "_output_error3";
            if (dst_p < dst_COPYLENGTH) {
                _i = SecureCopy(dst, dst_ref, dst_p, dst_COPYLENGTH);
                dst_ref += _i;
                dst_p += _i;
            }

            while (dst_p < dst_cpy) dst[dst_p++] = dst[dst_ref++];
            dst_p = dst_cpy;
            continue;
        }

        if (dst_p < dst_cpy) {
            SecureCopy(dst, dst_ref, dst_p, dst_cpy);
        }
        dst_p = dst_cpy;
    }


    return ((src_p) - src_0);
}

let ushortPool: Uint16Array | undefined;
let intPool: Int32Array | undefined;

function GetUShortHashTablePool(): Uint16Array {
    if (ushortPool === undefined) {
        ushortPool = new Uint16Array(HASH64K_TABLESIZE);
    }
    else {
        ushortPool.fill(0);
    }
    return ushortPool;
}
function GetIntHashTablePool() {
    if (intPool === undefined) {
        intPool = new Int32Array(HASH_TABLESIZE);
    }
    else {
        intPool.fill(0);
    }
    return intPool;
}

function compressCtx_safe32(hash_table: Int32Array, src: Uint8Array, dst: Uint8Array, src_0: number, dst_0: number, src_len: number, dst_maxlen: number) {
    const debruijn32 = DEBRUIJN_TABLE_32;
    let _i;



    let src_p = src_0;
    const src_base = src_0;
    let src_anchor = src_p;
    const src_end = src_p + src_len;
    const src_mflimit = src_end - MFLIMIT;

    let dst_p = dst_0;
    const dst_end = dst_p + dst_maxlen;

    const src_LASTLITERALS = src_end - LASTLITERALS;
    const src_LASTLITERALS_1 = src_LASTLITERALS - 1;

    const src_LASTLITERALS_STEPSIZE_1 = src_LASTLITERALS - (STEPSIZE_32 - 1);
    const dst_LASTLITERALS_1 = dst_end - (1 + LASTLITERALS);
    const dst_LASTLITERALS_3 = dst_end - (2 + 1 + LASTLITERALS);

    let length: number;

    let h: number, h_fwd: number;


    if (src_len < MINLENGTH) return _last_literals();


    hash_table[(Peek4(src, src_p) * 2654435761) >>> HASH_ADJUST] = src_p - src_base;
    src_p++;
    h_fwd = (Peek4(src, src_p) * 2654435761) >>> HASH_ADJUST;

    let tmp_findMatchAttempts = 0, tmp_src_p_fwd = 0, tmp_src_ref = 0, tmp_dst_token = 0;
    let tmp_donot_skip = true;


    while (true) {
        let findMatchAttempts = (1 << SKIPSTRENGTH) + 3;
        let src_p_fwd = src_p;
        let src_ref: number;
        let dst_token: number;
        if (tmp_donot_skip) {

            do {
                h = h_fwd;
                let step = findMatchAttempts++ >>> SKIPSTRENGTH;
                src_p = src_p_fwd;
                src_p_fwd = src_p + step;

                if (src_p_fwd > src_mflimit) return _last_literals();

                h_fwd = (((Peek4(src, src_p_fwd)) * 2654435761) >>> HASH_ADJUST);
                src_ref = src_base + hash_table[h];
                hash_table[h] = (src_p - src_base);
            } while ((src_ref < src_p - MAX_DISTANCE) || (!Equal4(src, src_ref, src_p)));


            while ((src_p > src_anchor) && (src_ref > src_0) && (src[src_p - 1] === src[src_ref - 1])) {
                src_p--;
                src_ref--;
            }


            length = (src_p - src_anchor);
            dst_token = dst_p++;

            if (dst_p + length + (length >>> 8) > dst_LASTLITERALS_3) return 0;

            let skip = length - RUN_MASK <= 254;
            if (length >= RUN_MASK) {
                let len = length - RUN_MASK;
                dst[dst_token] = (RUN_MASK << ML_BITS);
                if (len > 254) {
                    do {
                        dst[dst_p++] = 255;
                        len -= 255;
                    } while (len > 254);
                    dst[dst_p++] = len;
                    BlockCopy(src, src_anchor, dst, dst_p, length);
                    dst_p += length;

                }
                else dst[dst_p++] = len;
            }
            else { dst[dst_token] = length << ML_BITS; }


            if (length > 0 && skip) {
                WildCopy(src, src_anchor, dst, dst_p, (_i = dst_p + length));
                dst_p = _i;
            }
        }
        else {
            dst_token = tmp_dst_token;
            findMatchAttempts = tmp_findMatchAttempts;
            src_p_fwd = tmp_src_p_fwd;
            src_ref = tmp_src_ref;
            tmp_donot_skip = true;
        }



        Poke2(dst, dst_p, src_p - src_ref);
        dst_p += 2;


        src_p += MINMATCH;
        src_ref += MINMATCH;
        src_anchor = src_p;

        let no_skip = true;
        while (src_p < src_LASTLITERALS_STEPSIZE_1) {
            let diff = Xor4(src, src_ref, src_p);
            if (diff === 0) {
                src_p += STEPSIZE_32;
                src_ref += STEPSIZE_32;
                continue;
            }
            src_p += debruijn32[((diff & -diff) * 0x077CB531) >>> 27];
            no_skip = false;
            break;

        }
        if (no_skip) {
            if ((src_p < src_LASTLITERALS_1) && (Equal2(src, src_ref, src_p))) {
                src_p += 2;
                src_ref += 2;
            }
            if ((src_p < src_LASTLITERALS) && (src[src_ref] === src[src_p])) src_p++;
        }
        else no_skip = true;


        length = (src_p - src_anchor);

        if (dst_p + (length >>> 8) > dst_LASTLITERALS_1) return 0;

        if (length >= ML_MASK) {
            dst[dst_token] += ML_MASK;
            length -= ML_MASK;
            for (; length > 509; length -= 510) {
                dst[dst_p++] = 255;
                dst[dst_p++] = 255;
            }
            if (length > 254) {
                length -= 255;
                dst[dst_p++] = 255;
            }
            dst[dst_p++] = length;
        }
        else {
            dst[dst_token] += length;
        }


        if (src_p > src_mflimit) {
            src_anchor = src_p;
            return _last_literals();
        }


        hash_table[(Peek4(src, src_p - 2) * 2654435761) >>> HASH_ADJUST] = src_p - 2 - src_base;



        h = (Peek4(src, src_p) * 2654435761) >>> HASH_ADJUST;
        src_ref = src_base + hash_table[h];
        hash_table[h] = (src_p - src_base);

        if (src_ref > src_p - (MAX_DISTANCE + 1) && Equal4(src, src_ref, src_p)) {
            dst_token = dst_p++;
            dst[dst_token] = 0;
            {
                tmp_donot_skip = false;
                tmp_dst_token = dst_token;
                tmp_findMatchAttempts = findMatchAttempts;
                tmp_src_p_fwd = src_p_fwd;
                tmp_src_ref = src_ref;
            }
            continue;
        }


        src_anchor = src_p++;
        h_fwd = (Peek4(src, src_p) * 2654435761) >>> HASH_ADJUST;
    }

    function _last_literals(): number {
        let lastRun = src_end - src_anchor;
        if (dst_p + lastRun + 1 + ((lastRun + 255 - RUN_MASK) / 255) > dst_end) return 0;

        if (lastRun >= RUN_MASK) {
            dst[dst_p++] = (RUN_MASK << ML_BITS);
            lastRun -= RUN_MASK;
            for (; lastRun > 254; lastRun -= 255) dst[dst_p++] = 255;
            dst[dst_p++] = lastRun;
        }
        else dst[dst_p++] = lastRun << ML_BITS;
        BlockCopy(src, src_anchor, dst, dst_p, src_end - src_anchor);
        dst_p += src_end - src_anchor;
        return dst_p - dst_0;
    }
}

const forCalcU32 = new Uint32Array(1);
const forCalcU16 = new Uint16Array(forCalcU32.buffer);
const forCalcU8 = new Uint8Array(forCalcU32.buffer);

function bigTimeAndRshift_HASH64K_ADJUST(src: Uint8Array, index: number): number {
    forCalcU32[0] = Peek4(src, index);
    forCalcU32[0] *= 2654435761;
    forCalcU32[0] >>>= HASH64K_ADJUST;
    return forCalcU32[0];
}

function compress64kCtx_safe32(hash_table: Uint16Array, src: Uint8Array, dst: Uint8Array, src_0: number, dst_0: number, src_len: number, dst_maxlen: number): number {
    const debruijn32 = DEBRUIJN_TABLE_32;
    const bg = bigTimeAndRshift_HASH64K_ADJUST;



    let src_p = src_0;
    let src_anchor = src_p;
    const src_base = src_p;
    const src_end = src_p + src_len;
    const src_mflimit = src_end - MFLIMIT;

    let dst_p = dst_0;
    const dst_end = dst_p + dst_maxlen;

    const src_LASTLITERALS = src_end - LASTLITERALS;
    const src_LASTLITERALS_1 = src_LASTLITERALS - 1;

    const src_LASTLITERALS_STEPSIZE_1 = src_LASTLITERALS - (STEPSIZE_32 - 1);
    const dst_LASTLITERALS_1 = dst_end - (1 + LASTLITERALS);
    const dst_LASTLITERALS_3 = dst_end - (2 + 1 + LASTLITERALS);

    let len, length;

    let h;


    if (src_len < MINLENGTH) _last_literals();


    let h_fwd = bg(src, ++src_p);

    let tmp_findMatchAttempts = 0, tmp_src_p_fwd = 0, tmp_src_ref = 0, tmp_dst_token = 0;
    let tmp_donot_skip = true;

    while (true) {
        let findMatchAttempts = (1 << SKIPSTRENGTH) + 3;
        let src_p_fwd = src_p;
        let src_ref;
        let dst_token;
        if (tmp_donot_skip) {

            do {
                h = h_fwd;
                const step = (findMatchAttempts++ >>> SKIPSTRENGTH) & 0xffffffff;
                src_p = src_p_fwd;
                src_p_fwd = src_p + step;

                if (src_p_fwd > src_mflimit) return _last_literals();

                h_fwd = bg(src, src_p_fwd);
                src_ref = src_base + hash_table[h];
                hash_table[h] = (src_p - src_base);
            } while (!Equal4(src, src_ref, src_p));


            while ((src_p > src_anchor) && (src_ref > src_0) && (src[src_p - 1] === src[src_ref - 1])) {
                src_p--;
                src_ref--;
            }


            length = (src_p - src_anchor);
            dst_token = dst_p++;

            if (dst_p + length + (length >>> 8) > dst_LASTLITERALS_3) return 0;

            let no_skip2 = true;
            if (length >= RUN_MASK) {
                len = length - RUN_MASK;
                dst[dst_token] = (RUN_MASK << ML_BITS);
                if (len > 254) {
                    do {
                        dst[dst_p++] = 255;
                        len -= 255;
                    } while (len > 254);
                    dst[dst_p++] = len;
                    BlockCopy(src, src_anchor, dst, dst_p, length);
                    dst_p += length;
                    no_skip2 = false;

                }
                else {
                    dst[dst_p++] = len;
                }
            }
            else {
                dst[dst_token] = (length << ML_BITS);
            }


            if (length > 0 && no_skip2) {
                const _i = dst_p + length;
                WildCopy(src, src_anchor, dst, dst_p, _i);
                dst_p = _i;
            }
        }
        else {
            dst_token = tmp_dst_token;
            findMatchAttempts = tmp_findMatchAttempts;
            src_p_fwd = tmp_src_p_fwd;
            src_ref = tmp_src_ref;
            tmp_donot_skip = true;
        }


        forCalcU16[0] = src_p;
        forCalcU16[0] -= src_ref;
        Poke2(dst, dst_p, forCalcU16[0]);
        dst_p += 2;


        src_p += MINMATCH;
        src_ref += MINMATCH;
        src_anchor = src_p;
        let no_skip = true;
        while (src_p < src_LASTLITERALS_STEPSIZE_1) {
            const diff = Xor4(src, src_ref, src_p);
            if (diff === 0) {
                src_p += STEPSIZE_32;
                src_ref += STEPSIZE_32;
                continue;
            }
            src_p += debruijn32[((diff & -diff) * 0x077CB531) >>> 27];
            no_skip = false;
            break;

        }
        if (no_skip) {
            if ((src_p < src_LASTLITERALS_1) && (Equal2(src, src_ref, src_p))) {
                src_p += 2;
                src_ref += 2;
            }
            if ((src_p < src_LASTLITERALS) && (src[src_ref] === src[src_p])) src_p++;
        }
        no_skip = true;



        len = (src_p - src_anchor);

        if (dst_p + (len >>> 8) > dst_LASTLITERALS_1) return 0;

        if (len >= ML_MASK) {
            dst[dst_token] += ML_MASK;
            len -= ML_MASK;
            for (; len > 509; len -= 510) {
                dst[dst_p++] = 255;
                dst[dst_p++] = 255;
            }
            if (len > 254) {
                len -= 255;
                dst[dst_p++] = 255;
            }
            dst[dst_p++] = len;
        }
        else {
            dst[dst_token] += len;
        }


        if (src_p > src_mflimit) {
            src_anchor = src_p;
            return _last_literals();
        }


        hash_table[bg(src, src_p - 2)] = src_p - 2 - src_base;



        h = bg(src, src_p);
        src_ref = src_base + hash_table[h];
        hash_table[h] = (src_p - src_base);

        if (Equal4(src, src_ref, src_p)) {
            dst_token = dst_p++;
            dst[dst_token] = 0;
            {
                tmp_donot_skip = false;
                tmp_dst_token = dst_token;
                tmp_findMatchAttempts = findMatchAttempts;
                tmp_src_p_fwd = src_p_fwd;
                tmp_src_ref = src_ref;
            }
            continue;
        }


        src_anchor = src_p++;
        h_fwd = bg(src, src_p);
    }

    function _last_literals() {

        let lastRun = (src_end - src_anchor);
        if (dst_p + lastRun + 1 + (lastRun - RUN_MASK + 255) / 255 > dst_end) return 0;
        if (lastRun >= RUN_MASK) {
            dst[dst_p++] = (RUN_MASK << ML_BITS);
            lastRun -= RUN_MASK;
            for (; lastRun > 254; lastRun -= 255) dst[dst_p++] = 255;
            dst[dst_p++] = lastRun;
        }
        else {
            dst[dst_p++] = (lastRun << ML_BITS);
        }
        BlockCopy(src, src_anchor, dst, dst_p, src_end - src_anchor);
        dst_p += src_end - src_anchor;


        return ((dst_p) - dst_0);
    }
}


export function encode(input: Uint8Array, inputOffset: number, inputLength: number, output: Uint8Array, outputOffset: number, outputLength: number): number {
    CheckArguments(input, inputOffset, inputLength, output, outputOffset, outputLength);
    if (outputLength === 0) return 0;

    if (inputLength < LZ4_64KLIMIT) {
        return compress64kCtx_safe32(GetUShortHashTablePool(), input, output, inputOffset, outputOffset, inputLength, outputLength);
    }
    else {
        return compressCtx_safe32(GetIntHashTablePool(), input, output, inputOffset, outputOffset, inputLength, outputLength);
    }
}
