#!/bin/env python3

"""Script for testing against Python's binhex module"""

import base64
import sys
import warnings
from argparse import ArgumentParser, FileType, Namespace
from io import BytesIO
from tempfile import NamedTemporaryFile
from typing import BinaryIO, Final

BASE64_CHARS: Final = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
BINHEX_CHARS: Final = b"!\"#$%&'()*+,-012345689@ABCDEFGHIJKLMNPQRSTUVXYZ[`abcdefhijklmpqr"
BASE642BINHEX: Final = bytes.maketrans(BASE64_CHARS, BINHEX_CHARS)
BINHEX2BASE64: Final = bytes.maketrans(BINHEX_CHARS, BASE64_CHARS)


def _encode_hqx(data: bytes, output: BinaryIO):
    b64 = base64.b64encode(data)
    encoded = memoryview(b":" + b64.translate(BASE642BINHEX, delete=b"="))
    output.write(b"(This file must be converted with BinHex 4.0)\r")
    while True:
        nbytes = min(64, len(encoded))
        if nbytes == 0:
            break
        output.write(b"\r")
        output.write(encoded[:nbytes])
        encoded = encoded[nbytes:]
    output.write(b":\r")


def _decode_hqx(data: bytes, output: BinaryIO):
    data = data[data.index(b":") + 1:data.rindex(b":")]
    b64 = data.translate(BINHEX2BASE64, delete=b"\r\n")
    padding = (len(b64) * 6) % 8
    if padding == 4:
        b64 += b"=="
    elif padding == 2:
        b64 += b"="
    else:
        raise ValueError("invalid padding")
    output.write(base64.b64decode(b64, validate=True))


def encode(args: Namespace):
    """Encode compressed BinHex data using the binhex character encoding"""
    _encode_hqx(args.input.read(), args.output)


def decode(args: Namespace):
    """Decode compressed BinHex data using the binhex character encoding"""
    _decode_hqx(args.input.read(), args.output)


def extract(args: Namespace):
    """Extract the data fork from compressed BinHex data"""
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", DeprecationWarning)
        from binhex import hexbin
    hqx = BytesIO()
    _encode_hqx(args.input.read(), hqx)
    hqx.seek(0)
    with NamedTemporaryFile("x+b") as tempfile:
        hexbin(hqx, tempfile.name)
        data = tempfile.read()
    args.output.write(data)


ACTIONS: Final = {
    "encode": encode,
    "decode": decode,
    "extract": extract
}

PARSER: Final = ArgumentParser(description=__doc__)
_subparsers = PARSER.add_subparsers(
    required=True,
    help="Available operations"
)
for action, func in ACTIONS.items():
    _subparser = _subparsers.add_parser(action, help=func.__doc__)
    _subparser.add_argument(
        "input",
        type=FileType("rb"),
        help="Input destination"
    )
    _subparser.add_argument(
        "-o",
        "--output",
        type=FileType("wb"),
        default=sys.stdout.buffer,
        help="Output destination"
    )
    _subparser.set_defaults(func=func)


if __name__ == "__main__":
    _args = PARSER.parse_args()
    _args.func(_args)
