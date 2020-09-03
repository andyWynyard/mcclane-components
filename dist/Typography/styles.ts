import { StyledSystemProps } from '../GenericComponent'

interface TypographyStyles {
  H1: StyledSystemProps
  H2: StyledSystemProps
  H3: StyledSystemProps
  H4: StyledSystemProps
  H5: StyledSystemProps
  LeadLarge: StyledSystemProps
  LeadSmall: StyledSystemProps
  Paragraph: StyledSystemProps
  ParagraphSmall: StyledSystemProps
  Link: StyledSystemProps
}

export const typographyStyles: TypographyStyles = {
  H1: {
    as: 'h1',
  },
  H2: {
    as: 'h2',
  },
  H3: {
    as: 'h3',
  },
  H4: {
    as: 'h4',
  },
  H5: {
    as: 'h5',
  },
  LeadSmall: {
    as: 'p',
  },
  LeadLarge: {
    as: 'p',
  },
  Paragraph: {
    as: 'p',
  },
  ParagraphSmall: {
    as: 'p',
  },
  Link: {},
}
