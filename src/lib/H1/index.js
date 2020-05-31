import styled from 'styled-components'

const H1 = styled.h1`
  background-color: ${(props) => props.backgroundColor || 'transparent'};
  color: ${(props) => props.theme.textColor || '#000'};
`

export default H1
