from pydantic import BaseModel


class TranslationResponse(BaseModel):
    percentage_translated: float
    foreseeable_issues: list[str]
    lean_translation: str
    mistake_tally: dict[str, int]
