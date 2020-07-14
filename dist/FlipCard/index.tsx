import React from 'react'
import styled from 'styled-components'
import GenericComponent, { StyledSystemProps } from '../GenericComponent'
import { transparentize } from 'polished'
import Typography from '../Typography'
import { down } from 'styled-breakpoints'

const { H2, H4, Paragraph } = Typography
// eslint-disable-next-line @typescript-eslint/no-empty-interface
interface FlipCardProps extends StyledSystemProps {
  image: string
  listItems: string[]
  headingText: string
  value: string
  startColor?: string
  endColor?: string
}

interface HeadingProps extends StyledSystemProps {
  startColor?: string
  endColor?: string
}

type FlipCardWrapperProps = {
  image: string
  startColor?: string
  endColor?: string
}

const FlipCardWrapper = styled(GenericComponent)<FlipCardWrapperProps>`
  perspective: 1500px;
  position: relative;
  height: 520px;

  ${down('xl')} {
    height: auto;
    box-shadow: 0 1.5rem 4rem #00000033;
    background-color: #fff;
  }
  @media only screen and (hover: none) {
    height: auto;
    box-shadow: 0 1.5rem 4rem #00000033;
    background-color: #fff;
  }

  .front {
    height: 520px;
    transition: all 0.8s ease;
    position: absolute;
    top: 0;
    left: 0;
    width: 100%;
    backface-visibility: hidden;
    border-radius: 3px;
    overflow: hidden;
    box-shadow: 0 15px 40px #00000033;
    background-color: #fff;
    @media only screen and (hover: none) {
      height: auto;
      position: relative;
      box-shadow: none;
    }
    ${down('xl')} {
      height: auto;
      position: relative;
      box-shadow: none;
    }
  }

  .image {
    background-size: cover;
    height: 230px;
    background-blend-mode: screen;
    -webkit-clip-path: polygon(0 0, 100% 0, 100% 85%, 0 100%);
    clip-path: polygon(0 0, 100% 0, 100% 85%, 0 100%);
    border-top-left-radius: 3px;
    border-top-right-radius: 3px;

    background-image: linear-gradient(
        to right bottom,
        ${(props) =>
          props.startColor || props.theme.colors.primaryLight || '#7ed56f'},
        ${(props) =>
          props.endColor || props.theme.colors.primaryDark || '#28b485'}
      ),
      url(${(props) => props.image});
    background-position: center;
  }

  .back {
    height: 520px;
    transition: all 0.8s ease;
    position: absolute;
    top: 0;
    left: 0;
    width: 100%;
    -webkit-backface-visibility: hidden;
    backface-visibility: hidden;
    border-radius: 3px;
    overflow: hidden;
    box-shadow: 0 15px 40px #00000033;
    transform: rotateY(180deg);
    background-image: linear-gradient(
      to right bottom,
      ${(props) =>
        props.startColor || props.theme.colors.primaryLight || '#7ed56f'},
      ${(props) =>
        props.endColor || props.theme.colors.primaryDark || '#28b485'}
    );

    ${down('xl')} {
      transform: rotateY(0);
      height: auto;
      position: relative;
      clip-path: polygon(0 15%, 100% 0, 100% 100%, 0% 100%);
    }
    @media only screen and (hover: none) {
      transform: rotateY(0);
      height: auto;
      position: relative;
      clip-path: polygon(0 15%, 100% 0, 100% 100%, 0% 100%);
    }
    .back-content {
      display: flex;
      height: 520px;
      flex-direction: column;
      justify-content: space-evenly;
      padding: 0 50px;
      ${down('xl')} {
        height: auto;
        padding: 50px;
      }
      @media only screen and (hover: none) {
        height: auto;
        padding: 50px;
      }
    }
  }

  &:hover .front {
    transform: rotateY(-180deg);
    @media only screen and (hover: none) {
      transform: rotateY(0);
    }
    ${down('xl')} {
      transform: rotateY(0);
    }
  }

  &:hover .back {
    transform: rotateY(0);
  }
`

const Heading = styled(H4)<HeadingProps>`
  text-transform: uppercase;
  text-align: right;
  position: absolute;
  top: 120px;
  right: 4px;
  width: 75%;

  .heading-inner {
    line-height: 1.5;
    box-decoration-break: clone;
    padding: 8px 10px;
    background-image: linear-gradient(
      to right bottom,
      ${(props) =>
        transparentize(
          0.2,
          props.startColor || props.theme.colors.primaryLight || '#7ed56f'
        )},
      ${(props) =>
        transparentize(
          0.2,
          props.endColor || props.theme.colors.primaryDark || '#28b485'
        )}
    );
  }
`

const List = styled.div`
  padding: 30px;
  display: flex;
  flex-direction: row;
  align-items: flex-end;
  ul {
    list-style: none;
    width: 80%;
    margin: 0 auto;
    padding: 0;

    li {
      text-align: center;
      font-size: 15px;
      padding: 10px;

      &:not(:last-child) {
        border-bottom: 1px solid ${(props) => props.theme.colors.greyLight2};
      }
    }
  }
`

const Button = styled.button`
  border-radius: 100px;
  background-color: ${({ theme }) => theme.colors.white};
  border: none;
  text-transform: uppercase;
  cursor: pointer;
`

const FlipCard: React.FC<FlipCardProps> = ({
  image = `https://picsum.photos/id/1083/800/800`,
  headingText = 'Perfect for two',
  listItems = [
    'Romantic time',
    '2 tours',
    '4 days',
    'Luxury accomodation',
    'White beaches',
  ],
  value = '$300',
  startColor,
  endColor,
}) => {
  const renderListItems = (items: string[]) =>
    items.map((item) => (
      <li key={item}>
        <Paragraph color={`greyDark`} marginY={`XS`}>
          {item}
        </Paragraph>
      </li>
    ))
  return (
    <FlipCardWrapper image={image} startColor={startColor} endColor={endColor}>
      <div className="front">
        <div className="image" />
        <Heading
          startColor={startColor}
          endColor={endColor}
          color={`greyLight1`}
        >
          <span className="heading-inner">{headingText}</span>
        </Heading>
        <List>
          <ul>{renderListItems(listItems)}</ul>
        </List>
      </div>
      <div className="back">
        <div className="back-content">
          <H4
            margin={`NONE`}
            fontWeight={`300`}
            textAlign="center"
            color="white"
          >
            Just
          </H4>
          <H2
            marginY={`XL`}
            fontWeight={`100`}
            color="white"
            textAlign="center"
          >
            {value}
          </H2>
          <Button as="button">
            <Paragraph>Find out more!</Paragraph>
          </Button>
        </div>
      </div>
    </FlipCardWrapper>
  )
}

export default FlipCard
